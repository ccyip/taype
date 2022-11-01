{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Copyright: (c) 2022 Qianchuan Ye
-- SPDX-License-Identifier: MIT
-- Maintainer: Qianchuan Ye <yeqianchuan@gmail.com>
-- Stability: experimental
-- Portability: portable
--
-- Evaluate the oblivious testing programs.
module Main (main) where

import qualified Data.Csv as Csv
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import qualified Data.Vector as V
import Data.List (maximum)
import Options.Applicative
import System.IO (hClose, withBinaryFile)
import System.Process.Typed
import UnliftIO.Temporary (withSystemTempFile)

run :: Options -> IO ()
run options@Options {..} = do
  when (null optParties) $ error "Not enough parties"
  when (optRounds < 1) $ error "Not enough rounds"
  content <- readFileLBS optInput
  let v = case Csv.decode Csv.NoHeader content of
        Left s -> error $ toText s
        Right r -> r
  when (length v < 2) $ error "Not enough test cases"
  let hd = V.head v
      input = V.tail v

  log_ "Warm up"
  void $ run1 options hd $ V.head input
  -- Process each line. The output is in reverse order.
  output <- go hd (V.head input) (toList input) (1 :: Int) []
  let res =
        Csv.encode $
          ("stat" : ["public" | "public" <- hd])
            : (filterOutput ("stat" : hd) <$> reverse output)
  writeFileLBS optOutput res
  where
    go _ _ [] _ acc = return acc
    go hd prev (fields : input) i acc = do
      let fields' =
            zipWith
              (\field field' -> if field == "^" then field' else field)
              fields
              prev
      stats <- forM [1 .. optRounds] $ \j -> do
        log_ $ "Test case " <> show i <> " (round " <> show j <> ")"
        run1 options hd fields'
      let stat = sum stats `div` length stats
      go hd fields' input (i + 1) $ (show stat : fields') : acc
    filterOutput hd output =
      [ field
        | (party, field) <- zip hd output,
          party == "public" || party == "stat"
      ]

run1 :: Options -> [Text] -> [Text] -> IO Int
run1 Options {..} hd fields =
  withInput optParties hd fields $ \hs ->
    withManyProcessesWait_ (procs hs) go
  where
    go ps = do
      output <- forM ps $ \p ->
        let h = getStdout p
         in (,) <$> TIO.hGetLine h <*> TIO.hGetContents h
      stats <- forM output $ \(stat, content) -> do
        putTextLn stat
        putText content
        when (stat == "failed") $ error "Test failed"
        return $ readMaybe (toString stat) ?: (-1)
      return $ maximum stats
    procs = zipWith proc1 optParties
    proc1 party handle =
      setStdout createPipe $
        setStdin (useHandleClose handle) $
          proc optProg $
            toString party : optArgs

withInput :: [Text] -> [Text] -> [Text] -> ([Handle] -> IO a) -> IO a
withInput parties owners fields f = go [] parties
  where
    go hs [] = f (reverse hs)
    go hs (party : parties') =
      withSystemTempFile "input" $ \fp h -> do
        fillInput h party
        hClose h
        withBinaryFile fp ReadMode $ \h' ->
          go (h' : hs) parties'
    fillInput h party =
      zipWithM_ (TIO.hPutStrLn h <<$>> mkInput party) owners fields
    mkInput party owner field
      | owner == "public"
          || owner == "expected"
          || owner == party
          || party == "public" =
          owner <> ":" <> field
    mkInput _ owner _ = owner <> ":"

log_ :: Text -> IO ()
log_ msg = do
  putText "== "
  putText msg
  putTextLn " =="

withManyProcessesWait_ ::
  [ProcessConfig stdin stdout stderr] ->
  ([Process stdin stdout stderr] -> IO a) ->
  IO a
withManyProcessesWait_ configs f = go [] configs
  where
    go ps [] = f (reverse ps)
    go ps (config : configs') = do
      withProcessWait_ config $ \p -> go (p : ps) configs'

main :: IO ()
main = run =<< execParser (info (opts <**> helper) helpMod)
  where
    helpMod =
      fullDesc
        <> header "runner - evaluate the oblivious testing programs"

data Options = Options
  { optProg :: FilePath,
    optParties :: [Text],
    optRounds :: Int,
    optInput :: FilePath,
    optOutput :: FilePath,
    optArgs :: [String]
  }

opts :: Parser Options
opts = do
  optProg <-
    strArgument $
      metavar "PROGRAM" <> help "Testing program"
  parties <-
    strArgument $
      metavar "PARTIES" <> help "Participating parties, comma separated"
  optRounds <-
    argument auto $
      metavar "ROUNDS" <> help "How many rounds each test case is evaluated for"
  optInput <-
    strArgument $
      metavar "INPUT" <> help "Input file"
  optOutput <-
    strArgument $
      metavar "OUTPUT" <> help "Output file"
  optArgs <-
    many $
      strArgument $
        metavar "ARGS..." <> help "Extra arguments to the testing program"
  return Options {optParties = T.splitOn "," parties, ..}
