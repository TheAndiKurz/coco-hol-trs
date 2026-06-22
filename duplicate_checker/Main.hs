module Main where

import qualified Control.Monad
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
      let duplicate_systems = [(pair, mappings) | (pair, Success mappings) <- duplicate_results]

      let duplicate_systems_file_names = map (\(((s1, _), (s2, _)), model) -> (file_name s1, file_name s2, model)) duplicate_systems

      mapM_ (printDuplicateSystem verbose) duplicate_systems_file_names

      Control.Monad.when verbose $ do
        printStatistics $ map snd duplicate_results

printDuplicateSystem :: Bool -> (String, String, Mappings) -> IO ()
printDuplicateSystem True (fn1, fn2, mappings) = putStrLn $ yellow (fn1 ++ " == " ++ fn2) ++ "\n" ++ show mappings ++ "\n"
printDuplicateSystem False (fn1, fn2, _) = putStrLn $ fn1 ++ " == " ++ fn2

printStatistics :: [Duplicate_Checker_Result] -> IO ()
printStatistics results = do
  let (trivial, typeMapping, smt_fails, duplicates) = foldl tally (0, 0, 0, 0) results
      smt_calls = smt_fails + duplicates
      total = trivial + typeMapping + smt_fails + duplicates

  putStrLn "=== Duplicate Checker Statistics ==="
  putStrLn $ "Total Checks:        " ++ show total
  putStrLn $ "Trivial Fails:       " ++ show trivial
  putStrLn $ "Type Mapping Fails:  " ++ show typeMapping
  putStrLn $ "SMT Solver Calls:    " ++ show smt_calls
  putStrLn $ "SMT Fails:           " ++ show smt_fails
  putStrLn $ "Duplicates:          " ++ show duplicates
  putStrLn "===================================="
  where
    tally :: (Int, Int, Int, Int) -> Duplicate_Checker_Result -> (Int, Int, Int, Int)
    tally (t, tm, s, suc) TrivialFail = (t + 1, tm, s, suc)
    tally (t, tm, s, suc) TypeMappingFail = (t, tm + 1, s, suc)
    tally (t, tm, s, suc) SMTFail = (t, tm, s + 1, suc)
    tally (t, tm, s, suc) (Success _) = (t, tm, s, suc + 1)

red :: String -> String
red s = "\ESC[31m" ++ s ++ "\ESC[0m"

yellow :: String -> String
yellow s = "\ESC[33m" ++ s ++ "\ESC[0m"
