module Main (main) where

import qualified Taype
import Options.Applicative

opts :: Parser FilePath
opts = strArgument (metavar "FILE")

main :: IO ()
main = Taype.test =<< execParser (info (opts <**> helper) mempty)
