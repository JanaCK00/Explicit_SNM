module TestHelpers where

import Syntax
import SNModel
import qualified Data.Map.Strict as M
--import Data.Map.Strict ((!))
import qualified Data.Set as S
--import Data.Set (Set)
--import Data.List as L
import Semantics
import Test.QuickCheck
  ( Arbitrary (..), Property, classify, property, collect)
import Test.QuickCheck.Gen (genDouble)
import qualified Data.IntMap.Strict as IntMap

propo1 :: Form
propo1 = Adopted 1 (P 1)


--define some simple tautology
taut :: Form
taut = Disj [propo1, Neg propo1]


{-
check if a given SNModel maps every topic to a Relation and
in each Relation every agent to some set of friends (which may be empty)
-}
fullRel :: SNModel -> Bool
fullRel (SNM nrAgents' positions' rel' _) = (M.size rel' == M.size positions') && fullRelAgs rel' where
    fullRelAgs = all (\x -> IntMap.size x == nrAgents')


{-
check if a given SNModel maps every positions to a set of agents who have adopted it
(which may be empty)
-}
--fullVal :: SNModel -> Bool
--fullVal (SNM _ positions' _ val') = M.size val' == S.size (allPos positions')

--check if the set of agents in non-empty
nonEmptyAgs :: SNModel -> Bool
nonEmptyAgs (SNM 0 _ _ _ ) = False
nonEmptyAgs _              = True

--check if the dual maps all topics to a map where all agents are mapped
fullDual :: SNModel -> Bool
fullDual (SNM nrAgents' positions' _ dual') = (M.keys dual' == M.keys positions') && all ((== [1..nrAgents']) . IntMap.keys) dual'

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
disjointPositionSets (SNM _ positions' _ _) = S.size (S.unions positions') == foldr ((+) . S.size) 0 positions'


{-}
--check if everything that used to be modeled as a set has no duplicates in list-form
noDuplicates :: SNModel -> Bool
noDuplicates (SNM agents' positions' rel' val') = noDups agents' && all noDups positions' && all (all noDups) rel' && all noDups val' where
    noDups l = S.toList l == nub (S.toList l) --TODO remove toList after I've changed it
-}

--TODO extend if I write more
--check all properties at once
isValidSNModel :: SNModel -> Bool
isValidSNModel snm = all (\f -> f snm) [fullRel, nonEmptyAgs,
                                         nonEmptyPos,
                                        nonEmptyTpcs, disjointPositionSets]


--TODO is this the easiest way to have it use random taus??? (between 0 and 1), no can just genereate Double and take
newtype SpecialDouble = SpD Double deriving (Eq, Show)
instance Arbitrary SpecialDouble where
    arbitrary = SpD <$> genDouble

--check if for two consecutive Selecs, only the last applied matters
consecutiveSelec :: SNModel -> SpecialDouble -> SpecialDouble -> Bool
consecutiveSelec m (SpD d1) (SpD d2) = updSelecMatrix d1 m == updSelecMatrix d1 (updSelecMatrix d2 m)


--test if an Infl after a Selec 1 doesn't change anything
consInflSelecOne :: SNModel -> SpecialDouble  -> Bool
consInflSelecOne m (SpD d1) = updSelecMatrix 1 m == updInflPreComp d1 (updSelecMatrix 1 m) --(order is not accrordning to syntax ;))

--TODO check more things I did in simplify


--check if an application of Selec makes all relations reflexive
selecMakesRefl :: SNModel -> SpecialDouble -> Bool
selecMakesRefl m (SpD d1) = updSelecMatrix d1 m == makeReflModel (updSelecMatrix d1 m)


--check if an application of Selec makes all relations symmetric
selecMakesSym :: SNModel -> SpecialDouble -> Bool
selecMakesSym m (SpD d1) = updSelecMatrix d1 m == makeSymModel (updSelecMatrix d1 m)


--checks if a Form evaluates to the same as its simplified version on a given SNModel
simplifyWorks :: SNModel -> Form -> Bool
simplifyWorks m f = (m |= f) == (m |= simplify f)


--TODO add these to ExplicitSpec
--check if the constrcucted full relation is symmetric and reflexive on some given SNModel

symAndRefl :: SNModel -> Bool
symAndRefl m = (makeFullRelModel m == makeReflModel (makeFullRelModel m)) && (makeFullRelModel m == makeSymModel (makeFullRelModel m))

--check if a formula simplifies to Top or Bot
isTrivial :: Form -> Bool
isTrivial f = f' == Top || f' == Bot where
    f' = simplify f


--TODO delete !.!
prop_trivialForm :: Form -> Property
prop_trivialForm f =
  classify (isTrivial f) "simplifies to Top/Bot" $
    property True

prop_numberOfTurns :: Double -> SNModel -> Property
prop_numberOfTurns tau m =
    let steps = snd $ fixCount ((updInflPreComp tau'). (updSelecMatrix tau')) m
        tau' = snd $ properFraction tau in
        collect steps $
        property True

--check if a formula contains empty lists after Conj or Disj
containsEmpty :: Form -> Bool
containsEmpty (Conj xs) = null xs || any containsEmpty xs
containsEmpty (Disj xs) = null xs || any containsEmpty xs
containsEmpty (Infl _ f) = containsEmpty f
containsEmpty (Selec _ f) = containsEmpty f
containsEmpty (Impl f g) = containsEmpty f || containsEmpty g
containsEmpty (Neg f) = containsEmpty f
containsEmpty _ = False

--check if a simplified Form contains NO occurance of Top/Bot
topBotFree :: Form -> Bool
topBotFree = allSubf freePred where
    freePred (Infl _ f)     = allSubf freePred f
    freePred (Selec _ f)    = allSubf freePred f
    freePred (Adopted _ _ ) = True
    freePred (Connected {}) = True
    freePred _ = False --Includes Top, Bot (plus for the sake of pattern exhaustion, all complex cases, but those should be handled by allSubf)

--check if a simplified Form either simplifies to be trivial, or simplifies so it doesn't contain any occurances of Top/Bot
topBotpurity :: Form -> Bool
topBotpurity f = f' == Top || (f'== Bot || topBotFree f') where
    f' = simplify f