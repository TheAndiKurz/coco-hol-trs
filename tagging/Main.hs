module Main where

import qualified Control.Monad
import HRS (checkSystem)
import Parser
import System.Environment

flagAri :: Bool -> String -> IO ()
flagAri verbose file_name = do
  parseResult <- parseSystemFromFile file_name
  case parseResult of
    Left errors -> mapM_ (putStrLn . red . show) errors
    Right system -> do
      putStr $ file_name ++ ": "
      case checkSystem system of
        Left fail_msg -> putStrLn $ red fail_msg
        Right (flags, unused_globals) -> do
          print flags
          Control.Monad.when (verbose && not (null unused_globals)) $ do
            putStrLn $ yellow "Unused function symbols detected:"
            mapM_ (putStrLn . yellow . ("  " ++) . show) unused_globals

main :: IO ()
main = do
  cmd_args <- getArgs
  let verbose = "-v" `elem` cmd_args
  let file_args = filter (/= "-v") cmd_args

  mapM_ (flagAri verbose) file_args

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"
