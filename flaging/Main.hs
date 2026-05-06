{-# LANGUAGE DoAndIfThenElse      #-}

module Main where

import TRS
import Parser

main :: IO ()
main = do
    let file_name = "test.trs"
    content <- readFile file_name
    case runParser holSystemP $ newInput file_name content of
        Left errors -> mapM_ (putStrLn . red . show) errors
        Right (_, system) -> do
            print system
            case checkSystem system of 
                Left fail_msg -> putStrLn $ red fail_msg
                Right (flags, unused_globals) -> do
                    putStrLn $ show flags
                    if length unused_globals > 0 then do
                        putStrLn $ yellow $ "Unused global variables detected:"
                        mapM_ (putStrLn . yellow . ("  " ++) . show) unused_globals
                    else return ()



red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"


