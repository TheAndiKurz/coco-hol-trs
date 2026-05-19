module Main where

import TRS
import Parser
import System.Environment (getArgs)
import Data.List (nub, tails)
import Data.Either (partitionEithers)

main :: IO ()
main = do
    cmd_args <- getArgs
    let unique_args = nub cmd_args
    putStrLn $ show $ length unique_args
    parse_result <- mapM parseSystemFromFile unique_args

    let (errs, systems) = partitionEithers parse_result
    if not $ null errs then mapM_ (putStrLn . show) errs else do
    
    let preprocessed_systems = map preProcessSystemDuplicates systems

    let duplicate_systems = [ (s1, s2) 
                            | (s1:rest) <- tails preprocessed_systems
                            , s2 <- rest 
                            , duplicate s1 s2
                            ]

    mapM_ (putStrLn . (++ "\n\n") . show) duplicate_systems
    return ()


red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"


