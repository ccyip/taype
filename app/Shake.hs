{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Build system.
module Main (main) where

import qualified Data.String as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Development.Shake
import Development.Shake.FilePath
import System.Console.GetOpt
import qualified Text.Read as R

main :: IO ()
main = shakeArgsWith shakeOptions {shakeColor = True} flags $
  \args targets -> return $ Just $ do
    let rules = mkRules args
    if null targets then rules else want targets >> withoutActions rules
  where
    flags =
      [ Option
          ""
          ["round"]
          ( ReqArg
              (\s -> R.readEither s <&> \v opts -> opts {optRound = v})
              "ROUND"
          )
          "How many rounds each test case is evaluated for",
        Option
          ""
          ["out-dir"]
          ( ReqArg
              (\s -> Right $ \opts -> opts {optOutputDir = s})
              "OUTDIR"
          )
          "Path to the output directory"
      ]
    mkRules args = do
      let Options {optRound = rnd, optOutputDir = outDir} =
            flipfoldl' ($) defaultOptions args
      examples <- getExamples
      rulesForCommon
      bins <- foldMapM rulesForExample examples
      want bins

      "clean" ~> do
        need $ "clean/common" : (("clean/" <>) <$> examples)

      mapM_ (rulesForRunner rnd outDir) examples

      "run" ~> do
        need $ ("run/" <>) <$> examples

      "run/clean" ~> do
        removeFilesAfter outDir ["//"]

      "cleanall" ~> do
        need ["clean", "run/clean"]
        ShakeOptions {shakeFiles} <- getShakeOptions
        removeFilesAfter shakeFiles ["//*"]

data Options = Options
  { optRound :: Int,
    optOutputDir :: FilePath
  }

defaultOptions :: Options
defaultOptions =
  Options
    { optRound = 1,
      optOutputDir = exampleDir </> "output"
    }

drivers :: [String]
drivers = ["plaintext", "emp"]

exampleDir :: FilePath
exampleDir = "examples"

commonDir :: FilePath
commonDir = exampleDir </> "common"

taypeCmd :: [String] -> Action ()
taypeCmd args = do
  flags <- getEnv "TAYPE_FLAGS"
  command_ [Traced "TAYPE"] "cabal" $
    ["run", "taype", "--"] <> maybe [] S.words flags <> args

runnerCmd :: [String] -> Action ()
runnerCmd args =
  command_ [Traced "RUNNER"] "cabal" $ ["run", "runner", "--"] <> args

mlCmd :: [String] -> Action ()
mlCmd args =
  command_ [Traced "OCAMLOPT"] "ocamlfind" $ ["ocamlopt"] <> args

garbages :: [FilePattern]
garbages = ["*.cmi", "*.cmx", "*.o", "*.tpc", "*.oil"]

getExamples :: MonadIO m => m [FilePath]
getExamples = do
  files <- liftIO $ getDirectoryFilesIO exampleDir ["*/*.tp"]
  return $ hashNub $ takeDirectory1 <$> files

getTaypeFilesIn :: MonadIO m => FilePath -> m [FilePath]
getTaypeFilesIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["*.tp"]

getMLFromTaype :: FilePath -> [FilePath]
getMLFromTaype file =
  [ prefix,
    prefix <> "_conceal",
    prefix <> "_reveal"
  ]
    <&> (<.> "ml")
  where
    prefix = dropExtension file

getTestSrcIn :: MonadIO m => FilePath -> m [FilePath]
getTestSrcIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["test_*.ml"]

mkTestBin :: FilePath -> String -> FilePath
mkTestBin file driver = file <> "_" <> driver <.> exe

rulesForExample :: FilePath -> Rules [FilePath]
rulesForExample example = do
  let dir = exampleDir </> example
  tpNames <- getTaypeFilesIn example
  mls <- foldMapM rulesFromTaypeFile $ (dir </>) <$> tpNames
  srcNames <- getTestSrcIn example
  helpers <- liftIO $ (dir </>) <<$>> getDirectoryFilesIO dir ["*helper.ml"]
  bins <- flip foldMapM srcNames $ \srcName ->
    forM drivers $ \driver -> do
      let bin = mkTestBin (dir </> takeBaseName srcName) driver
          allMls =
            ((commonDir </>) <$> ["prelude.ml", "common.ml"])
              <> mls
              <> helpers
              <> [dir </> srcName]
      bin %> \out -> do
        need allMls
        mlCmd $
          [ "-o",
            out,
            "-linkpkg",
            "-package",
            "sexplib",
            "-package",
            "taype-driver-" <> driver,
            "-I",
            commonDir,
            "-I",
            dir
          ]
            <> allMls
      return bin

  ("build/" <> example) ~> need bins

  ("clean/" <> example) ~> do
    removeFilesAfter "." $ mls <> bins
    removeFilesAfter dir garbages
  return bins

rulesFromTaypeFile :: FilePath -> Rules [FilePath]
rulesFromTaypeFile tp = do
  let mls = getMLFromTaype tp
  mls &%> \_ -> do
    need [tp]
    taypeCmd [tp]
  return mls

rulesForCommon :: Rules ()
rulesForCommon = do
  let bin = commonDir </> "test"
      preludeML = commonDir </> "prelude.ml"

  bin %> \out -> do
    let mls = [preludeML, out <.> "ml"]
    need mls
    mlCmd $
      [ "-o",
        out,
        "-linkpkg",
        "-package",
        "taype-driver-plaintext"
      ]
        <> mls

  preludeML %> \out -> do
    taypeCmd ["--generate-prelude", dropExtension out]

  "build/common" ~> need [bin, preludeML]

  "clean/common" ~> do
    removeFilesAfter commonDir $ ["test", "prelude.ml"] <> garbages

getInputCsvIn :: MonadIO m => FilePath -> m [FilePath]
getInputCsvIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["*.input.csv"]

getSwitches :: MonadIO m => FilePath -> m (Maybe [String])
getSwitches file = do
  line <- liftIO $ withFile file ReadMode TIO.hGetLine
  return $ parseSwitches $ T.strip line

parseSwitches :: Text -> Maybe [String]
parseSwitches line = do
  line' <- T.stripPrefix "(*!" line
  let content = fromMaybe line' $ T.stripSuffix "*)" line'
      xs = T.splitOn ":" content
  case xs of
    [key, switches]
      | T.strip key == "switch" ->
          return $ T.splitOn "," switches <&> toString . T.strip
    _ -> Nothing

rulesForRunner :: Int -> FilePath -> FilePath -> Rules ()
rulesForRunner rnd outRoot example = do
  inputNames <- getInputCsvIn example
  let inDir = exampleDir </> example
      outDir = outRoot </> example
      tgt = "run/" <> example
  outputs <- flip foldMapM inputNames $ \inputName -> do
    let testName = dropExtensions inputName
        tgtWithName = tgt <> "/" <> testName
    switches <- getSwitches $ inDir </> testName <.> "ml"

    outputs <- flip foldMapM drivers $ \driver -> do
      let tgtWithDriver = tgtWithName <> "/" <> driver

      outputs <- forM (sequence switches) $ \switch -> do
        let input = inDir </> inputName
            outPath = outDir </> testName
            output =
              ( case switch of
                  Just s -> outPath <.> driver <.> s
                  _ -> outPath <.> driver
              )
                <.> "output"
                <.> "csv"
            isPlainText = driver == "plaintext"
            bin = mkTestBin (inDir </> testName) driver
            rnd' = if isPlainText then 1 else rnd

        output %> \out -> do
          unless isPlainText alwaysRerun
          need [bin, input]
          runnerCmd $
            [bin, partiesFromDriver driver, show rnd', input, out]
              <> maybeToList switch

        whenJust switch $ \o -> tgtWithDriver <> "/" <> o ~> need [output]
        return output
      tgtWithDriver ~> need outputs
      return outputs
    tgtWithName ~> need outputs
    return outputs
  tgt ~> need outputs

  "run/clean/" <> example ~> removeFilesAfter outDir ["*.output.csv"]

partiesFromDriver :: String -> String
partiesFromDriver "plaintext" = "public"
partiesFromDriver "emp" = "alice,bob"
partiesFromDriver _ = error "Unknown driver"
