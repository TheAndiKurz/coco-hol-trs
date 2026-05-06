module Main where

import TRS
import Parser

main :: IO ()
main = do
    Right system1 <- parseSystemFromFile "test.ari"
    Right system2 <- parseSystemFromFile "dhp_test.ari"

    print $ alphaEqual system1 system2

    return ()


red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"


