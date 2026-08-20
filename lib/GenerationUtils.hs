module GenerationUtils where
import Test.QuickCheck (Gen, chooseInt, elements, sublistOf)
import Data.Set (Set)
import qualified Data.Set as S


{-
This module provides helper functions for random generation.
-}


{-
Input:
lmin - lmax: range of length of returned list

Output:
Randomly chooses a length in the given range and returns a random sublist of the chosen length.
-}

sublistOfLength :: Ord a => Int -> Int -> [a] -> Gen [a]
sublistOfLength lmin lmax xs = do
    thisL <- chooseInt (lmin,lmax)
    sublistRec thisL xs

{-
Input:
l: desired length of output
xs: list

Output:
random subsequence of xs of length l
-}
sublistRec :: Eq a => Int -> [a] -> Gen [a]
sublistRec 0 _ = return []
sublistRec l xs = do
    if null xs then return [] --elements throws error if xs is empty
        else do el <- elements xs
                rest <- sublistRec (l-1) $ filter (/= el) xs --assuming we don't choose with replacement
                return $ el:rest



{-
Input:
l: number of partitions > 0
xs: list
(Assumptions: length xs >= l)

Output:
Generates a partition of xs with exactly l non-empty subsets.
-}
randomPart :: Int -> [a] -> Gen [[a]]
randomPart 1 xs = return [xs]
randomPart l xs = do
  let n = length xs
  thisLength <- chooseInt (1, n - l + 1) --make sure the rest of the (l-1) partitions still get at least one element each
  let (first, rest) = splitAt thisLength xs
  restPart <- randomPart (l-1) rest
  return $ first : restPart

{-
Checks if a given list has length between lower and upper.
Used in random generation for Form
-}
isOfSizeBetween :: Int -> Int -> [a] -> Bool
isOfSizeBetween lower upper xs = lower <= l &&  l <= upper where
  l = length xs


--deleted Arbitrary a from type class constraint, bc. I want to use is for Positions
subsetOf :: (Ord a) => Set a -> Gen (Set a)
subsetOf = fmap S.fromList . sublistOf . S.toList