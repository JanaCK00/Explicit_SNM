{-# LANGUAGE ImportQualifiedPost #-}



--TODO mark where I copied or adapted from SMCDEL

module SetTheory where

import SMCDEL.Internal.Help (lfp)
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
  , listOf1
  )
import Test.QuickCheck.Gen (suchThat)
import qualified Data.Vector as V
import Data.Vector (Vector) --vectors are 0-based!!

--Adapted from symbolic-topo-e-models.SetTheory.hs


--TODO describe what this file does ;)

type Agent = Int
type AgentSet = IntSet

type Relation = Vector AgentSet --represents a relation where at the i-th index we store the set of agents that are socially connected to agent i. an empty set if none
--assuming zero friends are rare, this gives O(1) access (adjacency set)



--Given a Relation, make it reflexive.
makeReflexive :: Relation -> Relation
makeReflexive = V.imap IntSet.insert



--Given a Relation, make it symmetric.
makeSymmetric :: Relation -> Relation
makeSymmetric rel = makeSym 0 (V.toList rel) rel where
  makeSym _ [] acc = acc
  makeSym i (ifriends:rest) acc = makeSym (i+1) rest (V.imap addMe acc) where
    addMe a f | a `IntSet.member` ifriends = IntSet.insert i f
              | otherwise                 = f

{-
  Recursively make a given relation transitive. For each agent, given their current
  friends group, add all agents reachable from any friend in their friends group
  until a fixpoint is reached.
-}
makeTransitive :: Relation -> Relation
makeTransitive rel = lfp makeTransOnce rel where
  makeTransOnce = V.map addRel
  addRel val = IntSet.unions [rel V.! w | w <- IntSet.toList val] `IntSet.union` val


combineRelation :: Relation -> Relation -> Relation
combineRelation = V.zipWith IntSet.union

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

isOfSizeBetween :: Int -> Int -> Set a -> Bool
isOfSizeBetween lower upper set = lower <= S.size set && S.size set <= upper

setSizeOf :: (Ord a) => Gen a -> Int -> Gen (Set a)
setSizeOf g k = fmap S.fromList (vectorOf k g)

subsetSizeOf :: (Ord a) => Set a -> Int -> Gen (Set a)
subsetSizeOf set k = fmap S.fromList (vectorOf k (setElements set))