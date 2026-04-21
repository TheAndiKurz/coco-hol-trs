module Main where

import TRS
import Parser

main :: IO ()
main = do
    content <- readFile "test.trs"
    case runParser holSystemP $ newInput content of
        Left errors -> print errors
        Right (_, system) -> do
            print system
            putStrLn "\n\n"
            print $ checkSystem system
