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
          (ReqArg R.readEither "ROUND")
          "How many rounds each test case is evaluated for"
      ]
    mkRules args = do
      let rnd = fromMaybe 1 $ viaNonEmpty last args
      examples <- getExamples
      rulesForCommon
      bins <- foldMapM rulesForExample examples
      want bins

      "clean" ~> do
        need $ "clean/common" : (("clean/" <>) <$> examples)

      mapM_ (rulesForRunner rnd) examples

      "run" ~> do
        need $ ("run/" <>) <$> examples

      "run/clean" ~> do
        need $ ("run/clean/" <>) <$> examples

      "cleanall" ~> do
        need ["clean", "run/clean"]
        ShakeOptions {shakeFiles} <- getShakeOptions
        removeFilesAfter shakeFiles ["//*"]

drivers :: [String]
drivers = ["plaintext", "emp"]

exampleDir :: FilePath
exampleDir = "examples"

commonDir :: FilePath
commonDir = exampleDir </> "common"

taypeCmd :: [String] -> Action ()
taypeCmd args =
  command_ [Traced "TAYPE"] "cabal" $ ["run", "taype", "--"] <> args

runnerCmd :: [String] -> Action ()
runnerCmd args =
  command_ [Traced "RUNNER"] "cabal" $ ["run", "runner", "--"] <> args

mlCmd :: [String] -> Action ()
mlCmd args =
  command_ [Traced "OCAMLOPT"] "ocamlfind" $ ["ocamlopt"] <> args

mlGarbages :: [FilePattern]
mlGarbages = ["*.cmi", "*.cmx", "*.o"]

getExamples :: MonadIO m => m [FilePath]
getExamples = do
  files <- liftIO $ getDirectoryFilesIO exampleDir ["*/*.tp"]
  return $ hashNub $ takeDirectory1 <$> files

getTaypeFilesIn :: MonadIO m => FilePath -> m [FilePath]
getTaypeFilesIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["*.tp"]

getMLFromTaype :: FilePath -> [FilePath]
getMLFromTaype file =
  [ replaceBaseName prefix "prelude",
    prefix,
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
            [commonDir </> "common.ml"]
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
    removeFilesAfter dir $ ["*.tpc", "*.oil"] <> mlGarbages
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
  bin %> \out -> do
    let mls = [out <.> "ml"]
    need mls
    mlCmd $ ["-o", out] <> mls

  "build/common" ~> need [bin]

  "clean/common" ~> do
    removeFilesAfter commonDir $ "test" : mlGarbages

getInputCsvIn :: MonadIO m => FilePath -> m [FilePath]
getInputCsvIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["*.input.csv"]

getOTypeOptions :: MonadIO m => FilePath -> m (Maybe [String])
getOTypeOptions file = do
  line <- liftIO $ withFile file ReadMode TIO.hGetLine
  return $ parseOTypeOptions $ T.strip line

parseOTypeOptions :: Text -> Maybe [String]
parseOTypeOptions line = do
  line' <- T.stripPrefix "(*!" line
  let content = fromMaybe line' $ T.stripSuffix "*)" line'
      xs = T.splitOn ":" content
  case xs of
    [key, options]
      | T.strip key == "otype" ->
          return $ T.splitOn "," options <&> toString . T.strip
    _ -> Nothing

rulesForRunner :: Int -> FilePath -> Rules ()
rulesForRunner rnd example = do
  inputNames <- getInputCsvIn example
  let dir = exampleDir </> example
      tgt = "run/" <> example
  outputs <- flip foldMapM inputNames $ \inputName -> do
    let name = dropExtensions inputName
        tgtWithName = tgt <> "/" <> name
    opts <- getOTypeOptions $ dir </> name <.> "ml"

    outputs <- flip foldMapM drivers $ \driver -> do
      let tgtWithDriver = tgtWithName <> "/" <> driver

      outputs <- forM (sequence opts) $ \opt -> do
        let input = dir </> inputName
            path = dir </> name
            output =
              ( case opt of
                  Just o -> path <.> driver <.> o
                  _ -> path <.> driver
              )
                <.> "output"
                <.> "csv"
            isPlainText = driver == "plaintext"
            bin = mkTestBin path driver
            rnd' = if isPlainText then 1 else rnd

        output %> \out -> do
          unless isPlainText alwaysRerun
          need [bin, input]
          runnerCmd $
            [bin, partiesFromDriver driver, show rnd', input, out]
              <> maybeToList opt

        whenJust opt $ \o -> tgtWithDriver <> "/" <> o ~> need [output]
        return output
      tgtWithDriver ~> need outputs
      return outputs
    tgtWithName ~> need outputs
    return outputs
  tgt ~> need outputs

  "run/clean/" <> example ~> removeFilesAfter dir ["*.output.csv"]

partiesFromDriver :: String -> String
partiesFromDriver "plaintext" = "public"
partiesFromDriver "emp" = "alice,bob"
partiesFromDriver _ = error "Unknown driver"
