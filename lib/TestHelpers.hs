module TestHelpers where

import Syntax
import SNModel
import qualified Data.Map.Strict as M
--import Data.Map.Strict ((!))
import qualified Data.Set as S
--import Data.Set (Set)
--import Data.List as L
import Semantics
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Test.QuickCheck
  ( Arbitrary (..))
import Test.QuickCheck.Gen (genDouble)
import SetTheory

propo1 :: Form
propo1 = PrpF (Adopted 1 (P 1))


--define some simple tautology
taut :: Form
taut = Disj [propo1, Neg propo1]


{-
check if a given SNModel maps every topic to a Relation and
in each Relation every agent to some set of friends (which may be empty)
-}
fullRel :: SNModel -> Bool
fullRel (SNM agents' positions' rel' _) = (M.size rel' == M.size positions') && fullRelAgs rel' where
    fullRelAgs = all (\x -> M.size x == IntSet.size agents')


{-
check if a given SNModel maps every positions to a set of agents who have adopted it
(which may be empty)
-}
fullVal :: SNModel -> Bool
fullVal (SNM _ positions' _ val') = M.size val' == S.size (allPos positions')

--check if the set of agents in non-empty
nonEmptyAgs :: SNModel -> Bool
nonEmptyAgs = not . IntSet.null . agents

--check if the set of topics in non-empty (by checking if the map isn't empty)
nonEmptyTpcs :: SNModel -> Bool
nonEmptyTpcs = not . null . positions

--check if the set of positions per topic in non-empty
nonEmptyPos :: SNModel -> Bool
nonEmptyPos = not . any null . positions

--doesn't make sense if the topic isnt a field in positions
--check if the positions maps a topic to a set containing only positions of that topic
{-validPositions :: SNModel -> Bool
validPositions (SNM _ positions' _ _) =  all everyPos (M.toList positions') where
    everyPos (tpc, pos) = all (\p -> posTopic p == tpc) pos
-}

--check if the sets of topics are pairwise disjoint
--TODO check if this is correct
disjointPositionSets :: SNModel -> Bool
disjointPositionSets (SNM _ positions' _ _) = S.size (allPos positions') == foldr ((+) . S.size) 0 positions'


{-}
--check if everything that used to be modeled as a set has no duplicates in list-form
noDuplicates :: SNModel -> Bool
noDuplicates (SNM agents' positions' rel' val') = noDups agents' && all noDups positions' && all (all noDups) rel' && all noDups val' where
    noDups l = S.toList l == nub (S.toList l) --TODO remove toList after I've changed it
-}

--TODO extend if I write more
--check all properties at once
isValidSNModel :: SNModel -> Bool
isValidSNModel snm = all (\f -> f snm) [fullRel, fullVal,
                                        nonEmptyAgs, nonEmptyPos,
                                        nonEmptyTpcs, disjointPositionSets]


--TODO is this the easiest way to have it use random taus???
newtype SpecialDouble = SpD Double deriving (Eq, Show)
instance Arbitrary SpecialDouble where
    arbitrary = SpD <$> genDouble

--check if for two consecutive Selecs, only the last applied matters
consecutiveSelec :: SNModel -> SpecialDouble -> SpecialDouble -> Bool
consecutiveSelec m (SpD d1) (SpD d2) = updSelec d1 m == updSelec d1 (updSelec d2 m)


--test if an Infl after a Selec 1 doesn't change anything
consInflSelecOne :: SNModel -> SpecialDouble  -> Bool
consInflSelecOne m (SpD d1) = updSelec 1 m == updInfl d1 (updSelec 1 m) --(order is not accrordning to syntax ;))

--TODO check more things I did in simplify


--check if an application of Selec makes all relations reflexive
selecMakesRefl :: SNModel -> SpecialDouble -> Bool
selecMakesRefl m (SpD d1) = updSelec d1 m == makeReflModel (updSelec d1 m)


--check if an application of Selec makes all relations symmetric
selecMakesSym :: SNModel -> SpecialDouble -> Bool
selecMakesSym m (SpD d1) = updSelec d1 m == makeSymModel (updSelec d1 m)


--checks if a Form evaluates to the same as its simplified version on a given SNModel
simplifyWorks :: SNModel -> Form -> Bool
simplifyWorks m f = (m |= f) == (m |= simplify f)


--TODO add these to ExplicitSpec
--check if the constrcucted full relation is symmetric and reflexive on some given SNModel

symAndRefl :: SNModel -> Bool
symAndRefl m = (makeFullRel m == makeReflModel (makeFullRel m)) && (makeFullRel m == makeSymModel (makeFullRel m))



