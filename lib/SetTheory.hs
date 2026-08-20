{-# LANGUAGE ImportQualifiedPost #-}



--TODO mark where I copied or adapted from SMCDEL
--TODO rename this file

module SetTheory where
import Data.Set
  ( Set
  )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Set qualified as S
import Test.QuickCheck
  ( Arbitrary
  , Gen
  , elements
  , listOf
  , oneof
  , sublistOf
  , vectorOf
  , listOf
  , listOf1, chooseInt
  )
import Test.QuickCheck.Gen (suchThat)

--Adapted from symbolic-topo-e-models.SetTheory.hs


--TODO describe what this file does ;)





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


-- Arbitrary Set Generation, based on existing functions for arbitrary list generation.

setOneOf :: Set (Gen a) -> Gen a
setOneOf = oneof . S.toList

--deleted Arbitrary a from type class constraint, bc. I want to use is for Positions
subsetOf :: (Ord a) => Set a -> Gen (Set a)
subsetOf = fmap S.fromList . sublistOf . S.toList

subsetOf1 :: (Arbitrary a, Ord a) => Set a -> Gen (Set a)
subsetOf1 xs = do
  getList <- sublistOf (S.toList xs) `suchThat` (not . null)
  return (S.fromList getList)

setOf :: (Arbitrary a, Ord a) => Gen a -> Gen (Set a)
setOf = fmap S.fromList . listOf

setOf1 :: (Arbitrary a, Ord a) => Gen a -> Gen (Set a)
setOf1 = fmap S.fromList . listOf1

setElements :: Set a -> Gen a
setElements = elements . S.toList

--added this for when type Agent = Int and sets of agents is IntSet
intSetElements :: IntSet -> Gen Int
intSetElements = elements . IntSet.toList

isOfSize :: Set a -> Int -> Bool
isOfSize set k = S.size set == k

isOfSizeBetween :: Int -> Int -> [a] -> Bool
isOfSizeBetween lower upper xs = lower <= l &&  l <= upper where
  l = length xs

setSizeOf :: (Ord a) => Gen a -> Int -> Gen (Set a)
setSizeOf g k = fmap S.fromList (vectorOf k g)

subsetSizeOf :: (Ord a) => Set a -> Int -> Gen (Set a)
subsetSizeOf set k = fmap S.fromList (vectorOf k (setElements set))