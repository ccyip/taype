{-# LANGUAGE OverloadedStrings #-}

-- |
-- Copyright: (c) 2022-2023 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Build system.
module Main (main) where

import Data.String qualified as S
import Development.Shake
import Development.Shake.FilePath
import System.Console.GetOpt
import Text.Read qualified as R

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
              (fmap (\v opts -> opts {optRound = v}) . R.readEither)
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
      mls <- foldMapM (rulesForExample outDir) examples
      want ["build"]

      "build" ~> do
        need mls
        mlCmd ["build"]

      "clean" ~> do
        need $ ("clean/" <>) <$> examples
        mlCmd ["clean"]

      mapM_ (rulesForRunner rnd outDir) examples

      "run" ~> do
        need $ ("run/" <>) <$> examples

      "cleanall" ~> do
        need ["clean"]
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

taypeCmd :: [String] -> Action CmdTime
taypeCmd args = do
  flags <- getEnv "TAYPE_FLAGS"
  command [Traced "TAYPE"] "cabal" $
    ["run", "taype", "--"] <> maybe [] S.words flags <> args

runnerCmd :: [String] -> Action ()
runnerCmd args =
  command_ [Traced "RUNNER"] "cabal" $ ["run", "runner", "--"] <> args

mlCmd :: [String] -> Action ()
mlCmd = command_ [Traced "DUNE", Cwd exampleDir] "dune"

garbages :: [FilePattern]
garbages = ["*.tpc", "*.oil", "*.sexp", "*.log", "*.stat"]

getExamples :: (MonadIO m) => m [FilePath]
getExamples = do
  files <- liftIO $ getDirectoryFilesIO exampleDir ["*/*.tp"]
  return $ hashNub $ takeDirectory1 <$> files

getTaypeFilesIn :: (MonadIO m) => FilePath -> m [FilePath]
getTaypeFilesIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["*.tp"]

getTestSrcIn :: (MonadIO m) => FilePath -> m [FilePath]
getTestSrcIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["test_*.ml"]

getBinPath :: FilePath -> FilePath -> FilePath
getBinPath example name = "_build" </> "default" </> example </> name <.> "exe"

rulesForExample :: FilePath -> FilePath -> Rules [FilePath]
rulesForExample outRoot example = do
  let dir = exampleDir </> example
  tpNames <- getTaypeFilesIn example
  mls <- mapM (rulesFromTaypeFile outRoot example) $ (dir </>) <$> tpNames
  srcNames <- getTestSrcIn example
  forM_ srcNames $ \srcName -> do
    let name = dropExtensions srcName
        bin = getBinPath example name
    ("build/" <> example <> "/" <> name) ~> do
      need mls
      mlCmd ["build", bin]

  ("build/" <> example) ~> do
    need mls
    mlCmd ["build", "@@" <> example <> "/default"]

  ("clean/" <> example) ~> do
    removeFilesAfter "." mls
    removeFilesAfter dir garbages
  return mls

rulesFromTaypeFile :: FilePath -> FilePath -> FilePath -> Rules FilePath
rulesFromTaypeFile outRoot example tp = do
  let ml = tp -<.> "ml"
      solverStat = tp -<.> ".solver.stat"
      solverStatFile = outRoot </> example </> takeFileName solverStat
      compileStatFile = outRoot </> example </> takeFileName tp -<.> ".compile.stat"
  ml %> \_ -> do
    alwaysRerun
    need [tp]
    CmdTime t <- taypeCmd [tp]
    copyFile' solverStat solverStatFile
    appendFile compileStatFile $ show t ++ "\n"
  return ml

getInputCsvIn :: (MonadIO m) => FilePath -> m [FilePath]
getInputCsvIn example =
  liftIO $ getDirectoryFilesIO (exampleDir </> example) ["*.input.csv"]

rulesForRunner :: Int -> FilePath -> FilePath -> Rules ()
rulesForRunner rnd outRoot example = do
  inputNames <- getInputCsvIn example
  let inDir = exampleDir </> example
      outDir = outRoot </> example
      tgt = "run/" <> example
  tgtWithNames <- forM inputNames $ \inputName -> do
    let testName = dropExtensions inputName
        buildTgt = "build/" <> example <> "/" <> testName
        bin = exampleDir </> getBinPath example testName
        tgtWithName = tgt <> "/" <> testName

    tgtWithDrivers <- forM drivers $ \driver -> do
      let input = inDir </> inputName
          output = outDir </> testName <.> driver <.> "output" <.> "csv"
          rnd' = if driver == "plaintext" then 1 else rnd
          tgtWithDriver = tgtWithName <> "/" <> driver

      tgtWithDriver ~> do
        need [buildTgt, input]
        runnerCmd
          [ bin,
            driver,
            partiesFromDriver driver,
            show rnd',
            input,
            output
          ]
      return (driver, tgtWithDriver)

    let tgts = [t | (driver, t) <- tgtWithDrivers, driver == "emp"]
    tgtWithName ~> need tgts
    return tgtWithName

  tgt ~> need tgtWithNames

partiesFromDriver :: String -> String
partiesFromDriver "plaintext" = "trusted"
partiesFromDriver "emp" = "alice,bob"
partiesFromDriver _ = error "Unknown driver"
