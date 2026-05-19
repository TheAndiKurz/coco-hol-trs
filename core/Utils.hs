module Utils where

import qualified Data.Set as Set

firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (x:xs)
      | Set.member x seen = Just x
      | otherwise         = go (Set.insert x seen) xs
