module Main where

import qualified Control.Monad
import HRS (checkSystem)
import Parser
import System.Environment

condPrint :: Bool -> String -> IO ()
condPrint False _ = return ()
condPrint True s = putStr s

flagAri :: Bool -> String -> IO ()
flagAri verbose file_name = do
  parseResult <- parseSystemFromFile file_name
  case parseResult of
    Left errors -> mapM_ (putStrLn . red . show) errors
    Right system -> do
      condPrint verbose $ show system
      putStr $ file_name ++ ": "
      case checkSystem system of
        Left fail_msg -> putStrLn $ red fail_msg
        Right (flags, unused_globals) -> do
          print flags
          Control.Monad.when (verbose && not (null unused_globals)) $ do
            putStrLn $ yellow "Unused global variables detected:"
            mapM_ (putStrLn . yellow . ("  " ++) . show) unused_globals

main :: IO ()
main = do
  cmd_args <- getArgs
  mapM_ (flagAri False) cmd_args

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"
