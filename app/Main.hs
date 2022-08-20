module Main (main) where

import Taype
import Taype.Environment
import Options.Applicative

opts :: Parser FilePath
opts = strArgument (metavar "FILE")

main :: IO ()
main = test defaultOptions =<< execParser (info (opts <**> helper) mempty)
