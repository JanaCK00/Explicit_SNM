{-# LANGUAGE ImportQualifiedPost #-}



--TODO mark where I copied or adapted from SMCDEL

module SetTheory where

import SMCDEL.Internal.Help (lfp)
import Data.Set
  ( Set
  , elemAt
  , intersection
  , union
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
  , listOf1
  )
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import Test.QuickCheck.Gen (suchThat)


--TODO describe what this file does ;)

type Agent = Int
type AgentSet = IntSet
type Relation = M.Map Agent AgentSet --every agent should be a key


{-
  Make a given relation reflexive. Given a world w (the key), add w to its own
  image (val).
-}

--adapted to fit my Relation definition
makeReflexive :: Relation -> Relation
makeReflexive = M.mapWithKey IntSet.insert

--TODO is checking better than the makeReflexive for testing?
--isReflexive :: Relation -> Bool
--isReflexive = M.foldrWithKey (\k s b -> (k `IntSet.member`s) && b) True


{- old version}
makeSymmetric :: Relation -> Relation
makeSymmetric rel = M.mapWithKey (\k s -> s `IntSet.union` friendsOfAg k) rel where
  friendsOfAg ag = IntSet.fromList $ filter (\k -> ag `IntSet.member` (rel ! k)) (M.keys rel)
-}


--TODO Check if this works
--given a Relation, make it symmetric
makeSymmetric :: Relation -> Relation
makeSymmetric rel = M.foldrWithKey addSym rel rel where -- TODO use strict fold? even necessaty if M is strict.map? I do! think so
    addSym ag friendsOfAg acc =
      foldr (\friend acc' -> M.insertWith IntSet.union friend (IntSet.singleton ag) acc') acc (IntSet.toList friendsOfAg) --TODO list conversion

{-
  Recursively make a given relation transitive. For each world, given its current
  image, add all worlds reachable from any world in its image to the current image
  until a fixpoint is reached.
-}

--TODO fix if needed, bc I changed Relation (right now it's as it was, only changed to IntSet)
makeTransitive :: Relation -> Relation
makeTransitive rel = lfp makeTransOnce rel where
  makeTransOnce = M.map addRel
  addRel val = IntSet.unions [rel ! w | w <- IntSet.toList val] `IntSet.union` val


-- Arbitrary Set Generation, based on existing functions for arbitrary list generation.

setOneOf :: Set (Gen a) -> Gen a
setOneOf = oneof . S.toList

subsetOf :: (Arbitrary a, Ord a) => Set a -> Gen (Set a)
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

isOfSizeBetween :: Int -> Int -> Set a -> Bool
isOfSizeBetween lower upper set = lower <= S.size set && S.size set <= upper

setSizeOf :: (Ord a) => Gen a -> Int -> Gen (Set a)
setSizeOf g k = fmap S.fromList (vectorOf k g)

subsetSizeOf :: (Ord a) => Set a -> Int -> Gen (Set a)
subsetSizeOf set k = fmap S.fromList (vectorOf k (setElements set))