module Main where

import Data.Either (partitionEithers)
import Data.List (nub, tails)
import HRS
import Parser
import System.Environment (getArgs)

main :: IO ()
main = do
  cmd_args <- getArgs
  let unique_args = nub cmd_args

  let verbose = "-v" `elem` unique_args
  let file_args = filter (/= "-v") unique_args

  parse_result <- mapM parseSystemFromFile file_args

  let (errs, systems) = partitionEithers parse_result
  if not $ null errs
    then mapM_ print errs
    else do
      let preprocessed_systems = map preProcessSystemDuplicates systems

      let system_pairs =
            [ (s1, s2)
              | (s1 : rest) <- tails preprocessed_systems,
                s2 <- rest
            ]
      duplicate_results <- mapM (\s -> (,) s <$> uncurry (duplicate "z3") s) system_pairs
      let duplicate_systems = [(pair, mappings) | (pair, Just mappings) <- duplicate_results]

      let duplicate_systems_file_names = map (\(((s1, _), (s2, _)), model) -> (file_name s1, file_name s2, model)) duplicate_systems

      mapM_ (printDuplicateSystem verbose) duplicate_systems_file_names

printDuplicateSystem :: Bool -> (String, String, Mappings) -> IO ()
printDuplicateSystem True (fn1, fn2, mappings) = putStrLn $ yellow (fn1 ++ " == " ++ fn2) ++ "\n" ++ show mappings ++ "\n"
printDuplicateSystem False (fn1, fn2, _) = putStrLn $ fn1 ++ " == " ++ fn2

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"
