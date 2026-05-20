module Main where

import TRS
import Parser
import System.Environment (getArgs)
import Data.List (nub, tails)
import Data.Either (partitionEithers)
import Control.Monad (filterM)

main :: IO ()
main = do
    cmd_args <- getArgs
    let unique_args = nub cmd_args
    parse_result <- mapM parseSystemFromFile unique_args

    let (errs, systems) = partitionEithers parse_result
    if not $ null errs then mapM_ (putStrLn . show) errs else do
    
    let preprocessed_systems = map preProcessSystemDuplicates systems

    let system_pairs = [ (s1, s2) 
                       | (s1:rest) <- tails preprocessed_systems
                       , s2 <- rest 
                       ]
    duplicate_systems <- filterM (uncurry $ duplicate "z3") system_pairs
    let duplicate_systems_file_names = map (\((s1,_), (s2,_)) -> (file_name s1, file_name s2)) duplicate_systems

    mapM_ (putStrLn . (\(fn1, fn2) -> fn1 ++ " =?= " ++ fn2)) duplicate_systems_file_names
    return ()


red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"


