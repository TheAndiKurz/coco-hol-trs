{-# LANGUAGE DoAndIfThenElse      #-}

module Main where

import TRS
import Parser
import System.Environment
import Data.List (sort)

flagsShow :: Flags -> String
flagsShow (Flags {second_order=so, pattern=prs, left_linear=ll, deterministic_pattern=dprs}) = 
    unwords [name | (True, name) <- [ (dprs, "DPRS")
                                    , (prs, "PRS")
                                    , (ll, "left-linear")
                                    , (so, "second-order") 
                                    ]]

flagAri :: String -> IO ()
flagAri file_name = do 
    parseResult <- parseSystemFromFile file_name
    case parseResult of
        Left errors -> mapM_ (putStrLn . red . show) errors
        Right system -> do
            putStr $ file_name ++ ": "
            case checkSystem system of 
                Left fail_msg -> putStrLn $ red fail_msg
                Right (flags, unused_globals) -> do
                    putStrLn $ flagsShow flags
                    if length unused_globals > 0 then do
                        putStrLn $ yellow $ "Unused global variables detected:"
                        mapM_ (putStrLn . yellow . ("  " ++) . show) unused_globals
                    else return ()

main :: IO ()
main = do
    cmd_args <- getArgs
    mapM_ flagAri $ sort cmd_args

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"


