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
  (Property, classify, property, collect)
import qualified Data.IntMap.Strict as IntMap
import SetTheory(Relation, makeTransitive, makeReflexive)
import qualified Data.IntSet as IntSet
import qualified Data.Vector as V

propo1 :: Form
propo1 = Adopted 1 (P 1)


--define some simple tautology
taut :: Form
taut = Disj [propo1, Neg propo1]


--TODO write this nicely!!! to check everything it needs to fullful -> put int SNModel
--TODO extend if I write more
--check all properties at once
isValidSNModel :: SNModel -> Bool
isValidSNModel snm = all (\f -> f snm) [fullRel, nonEmptyAgs,
                                         nonEmptyPos,
                                        nonEmptyTpcs, disjointPositionSets]


{-
check if a given SNModel maps every topic to a Relation and
in each Relation every agent to some set of friends (which may be empty)
-}
fullRel :: SNModel -> Bool
fullRel (SNM _ positions' rel' _) = M.size rel' == M.size positions'


--here to be falsified. checks if the dual always maps every agent
fullDual :: SNModel -> Bool
fullDual (SNM nrAgs' _ _ dual') = all (\dual_t -> IntMap.size dual_t == nrAgs') dual'

fullDualBasicInfl :: Double -> SNModel -> Bool
fullDualBasicInfl tau m = fullDual m' where
  m' = updInflBasic tau' m
  tau' = properTau tau

fullDualBasicSelec :: Double -> SNModel -> Bool
fullDualBasicSelec tau m = fullDual m' where
  m' = updSelecBasic tau' m
  tau' = properTau tau

fullDualVariantInfl :: Double -> SNModel -> Bool
fullDualVariantInfl tau m = fullDual m' where
  m' = updInflVariant tau' m
  tau' = properTau tau

fullDualVariantSelec :: Double -> SNModel -> Bool
fullDualVariantSelec tau m = fullDual m' where
  m' = updSelecVariant tau' m
  tau' = properTau tau

--check if the set of agents in non-empty
nonEmptyAgs :: SNModel -> Bool
nonEmptyAgs (SNM 0 _ _ _ ) = False
nonEmptyAgs _              = True


--check if the set of topics in non-empty (by checking if the map isn't empty)
nonEmptyTpcs :: SNModel -> Bool
nonEmptyTpcs = not . null . positions

--check if the set of positions per topic in non-empty
nonEmptyPos :: SNModel -> Bool
nonEmptyPos = not . any null . positions


--check if the dual doesn't maps an agent to an empty set
nonEmptyDualmapping :: SNModel -> Bool
nonEmptyDualmapping m = all noEmptyValue (dual m) where
  noEmptyValue = IntMap.foldr (\x acc -> x /= S.empty && acc) True


nonEmptyDualmappingBasicInfl :: Double -> SNModel -> Bool
nonEmptyDualmappingBasicInfl tau m = nonEmptyDualmapping m' where
  tau'= properTau tau
  m' = updInflBasic tau' m

nonEmptyDualmappingBasicSelec :: Double -> SNModel -> Bool
nonEmptyDualmappingBasicSelec tau m = nonEmptyDualmapping m' where
  tau'= properTau tau
  m' = updSelecBasic tau' m

nonEmptyDualmappingVariantInfl :: Double -> SNModel -> Bool
nonEmptyDualmappingVariantInfl tau m = nonEmptyDualmapping m' where
  tau'= properTau tau
  m' = updInflVariant tau' m

nonEmptyDualmappingVariantSelec :: Double -> SNModel -> Bool
nonEmptyDualmappingVariantSelec tau m = nonEmptyDualmapping m' where
  tau'= properTau tau
  m' = updSelecVariant tau' m

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





--check if an application of Selec makes all relations reflexive
selecMakesRefl :: SNModel -> Double -> Bool
selecMakesRefl m d1 = upM == makeReflModel upM where
    upM = updSelecBasic d1' m
    d1' = properTau d1

--check if an application of Selec Variant makes all relations reflexive
selecMakesReflVariant :: SNModel -> Double -> Bool
selecMakesReflVariant m d1 = upM == makeReflModel upM where
    upM = updSelecVariant d1' m
    d1' = properTau d1


--check if an application of Selec makes all relations symmetric
selecMakesSym :: SNModel -> Double -> Bool
selecMakesSym m d1 = updSelecBasic d1' m == makeSymModel (updSelecBasic d1' m) where
    d1' = properTau d1

--count how many steps until stable
--TODO does this work with the maybe returned in steps?
prop_numberOfTurns :: Double -> SNModel -> Property
prop_numberOfTurns tau m =
    let steps = snd $ stabCountSafe 100 ((updInflBasic tau'). (updSelecBasic tau')) m
        tau' = properTau tau in
        collect steps $
        property True


prop_numberOfTurnsVariant :: Double -> SNModel -> Property
prop_numberOfTurnsVariant tau m =
    let steps = snd $ fixCount ((updInflVariant tau'). (updSelecVariant tau')) m
        tau' = properTau tau in
        collect steps $
        property True

{-
SECTION Syntax
-}


--checks if a Form evaluates to the same as its simplified version on a given SNModel
simplifyWorks :: SNModel -> Form -> Bool
simplifyWorks m f = (m |= f) == (m |= simplify f)


--check if a formula simplifies to Top or Bot
isTrivial :: Form -> Bool
isTrivial f = f' == Top || f' == Bot where
    f' = simplify f


--Property to display percentage of generated Forms that are trivial
prop_trivialForm :: Form -> Property
prop_trivialForm f =
  classify (isTrivial f) "simplifies to Top/Bot" $
    property True


--check if a formula contains empty lists after Conj or Disj
containsEmpty :: Form -> Bool
containsEmpty (Conj xs) = null xs || any containsEmpty xs
containsEmpty (Disj xs) = null xs || any containsEmpty xs
containsEmpty (Infl _ _ f) = containsEmpty f
containsEmpty (Selec _ _ f) = containsEmpty f
containsEmpty (Impl f g) = containsEmpty f || containsEmpty g
containsEmpty (Neg f) = containsEmpty f
containsEmpty _ = False


--check if a simplified Form contains NO occurance of Top/Bot
topBotFree :: Form -> Bool
topBotFree = allSubf freePred where
    freePred (Infl _ _ f)     = allSubf freePred f
    freePred (Selec _ _ f)    = allSubf freePred f
    freePred (Adopted _ _ ) = True
    freePred (Connected {}) = True
    freePred _ = False --Includes Top, Bot (plus for the sake of pattern exhaustion, all complex cases, but those should be handled by allSubf)

--check if every formula either simplifies to Top/Bot or simplifies to be free of any occurance of top/bot
topBotpurity :: Form -> Bool
topBotpurity f = f' == Top || (f'== Bot || topBotFree f') where
    f' = simplify f


--check if for two consecutive Selecs, only the last applied matters
consecutiveSelec :: SNModel -> Double -> Double -> Bool
consecutiveSelec m d1 d2 = updSelecBasic d1' m == updSelecBasic d1' (updSelecBasic d2' m) where
    d1' = properTau d1
    d2' = properTau d2

properTau :: Double -> Double
properTau tau | isZeroFrac && odd intPart = 1
              | otherwise                    = fracPart
    where (intPart, fracPart) = properFraction tau
          isZeroFrac = abs fracPart < epsilon
          epsilon = 1e-12


--test if an Infl Basic after a Selec Basic 1 doesn't change anything
consInflSelecOne :: SNModel -> Double  -> Bool
consInflSelecOne m d1 = (updSelecBasic 1 m == updInflBasic d1' (updSelecBasic 1 m)) || d1' == 0.0 --(order is not accrordning to syntax ;))
    where d1' = properTau d1


--check if nr of reachable agents nerver grows for variant Selec
noGrowingReachable :: Double -> SNModel -> Bool
noGrowingReachable tau m = reachUpdated `smallerEqualThan` reachOriginal where
    upM = updSelecVariant tau' m
    tau' = properTau tau
    transClosure rel' = makeReflexive $ makeTransitive $ combinedTopicsRel (nrAgents m) rel'
    reachOriginal = transClosure $ rel m
    reachUpdated = transClosure $ rel upM

--check if friends in rel1 is subset of friends in rel2 for all agents
smallerEqualThan :: Relation -> Relation -> Bool
smallerEqualThan rel1 rel2 = (V.length rel1 == V.length rel2) && and (V.zipWith IntSet.isSubsetOf rel1 rel2)


--check if softer tau -> stronger tau leaves softer irrelevant
variantSelecGrowingTau :: Double -> Double ->  SNModel -> Bool
variantSelecGrowingTau d1 d2 m | d1'<= d2' = updSelecVariant d2' (updSelecVariant d1' m) == updSelecVariant d2' m
                               | otherwise = variantSelecGrowingTau d2 d1 m
    where
    d1' = properTau d1
    d2' = properTau d2


inflNotChangeRel :: Double -> SNModel -> Bool
inflNotChangeRel tau m = rel m == rel m' where
    m' = updInflBasic tau' m
    tau' = properTau tau

selecNotChangeDual :: Double -> SNModel -> Bool
selecNotChangeDual tau m = dual m == dual m' where
    m' = updSelecBasic tau' m
    tau' = properTau tau


inflVarNotChangeRel :: Double -> SNModel -> Bool
inflVarNotChangeRel tau m = rel m == rel m' where
    m' = updInflVariant tau' m
    tau' = properTau tau

selecVarNotChangeDual :: Double -> SNModel -> Bool
selecVarNotChangeDual tau m = dual m == dual m' where
    m' = updSelecVariant tau' m
    tau' = properTau tau


{-}
was just to check, both have been falsified

testmakeReflexive :: SNModel -> Bool
testmakeReflexive (SNM nrAgents' _ rel' _) = trans == makeReflexive trans where
    trans = makeTransitive $ combinedTopicsRel nrAgents' rel'

testcombinedTopicsRel :: SNModel -> Bool
testcombinedTopicsRel (SNM nrAgents' _ rel' _) = combo == makeReflexive combo where
    combo = combinedTopicsRel nrAgents' rel'
    -}


{-
SECTION
Hardcoded SNModels
-}

{-
(Example 2) from Smets et al. 2020  (all steps)
-}
exPaperstep0, exPaperstep1, exPaperstep2, exPaperstep3, exPaperstep4, exPaperstep5 :: SNModel
exPaperstep0 = examplePaper

exPaperstep1 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = V.fromList [IntSet.fromList [0..3], IntSet.fromList [0,1], IntSet.fromList [0,2,3], IntSet.fromList [0,2,3]]
  mRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.fromList [1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.singleton (P 2)), (2, S.fromList [P 1, P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDual = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 6, P 7]), (2, S.singleton (P 8)), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 12]), (3, S.fromList [P 9, P 10])]

exPaperstep2 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = V.fromList [IntSet.fromList [0..3], IntSet.fromList [0,1], IntSet.fromList [0,2,3], IntSet.fromList [0,2,3]]
  mRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.fromList [1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDual = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]

exPaperstep3 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = V.fromList [IntSet.fromList [0, 1, 2, 3], IntSet.fromList [0, 1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDual = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]

exPaperstep4 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = V.fromList [IntSet.fromList [0, 1, 2, 3], IntSet.fromList [0, 1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDual = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1, S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]

exPaperstep5 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = V.fromList [IntSet.fromList [0, 1, 3], IntSet.fromList [0, 1, 3], IntSet.singleton 2, IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDual = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1, S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]


{-
(Example 4) with corrected typo from Smets et al. 2020  (all steps)
-}

exPaperVarstep0, exPaperVarstep1, exPaperVarstep2, exPaperVarstep3, exPaperVarstep4, exPaperVarstep5 :: SNModel
exPaperVarstep0 = examplePaper
exPaperVarstep1 = exPaperstep1


exPaperVarstep2 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = V.fromList [IntSet.fromList [0..3], IntSet.fromList [0,1], IntSet.fromList [0,2,3], IntSet.fromList [0,2,3]]
  mRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.fromList [1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDual = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.singleton (P 5)), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11]), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]


exPaperVarstep3 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = makeFullRel 4
  sRel = makeFullRel 4
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDual = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.singleton (P 5)), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11]), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]

exPaperVarstep4 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = makeFullRel 4
  sRel = makeFullRel 4
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDual = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5, P 6, P 7]), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11,  P 12]), (2, S.fromList [P 9, P 10, P 11,  P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]

exPaperVarstep5 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = makeFullRel 4
  sRel = makeFullRel 4
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDual = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5, P 6, P 7]), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11,  P 12]), (2, S.fromList [P 9, P 10, P 11,  P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]

{-
Own example (interleaving of Variant Infl, Variant Selec)
-}

exOwnstep0, exOwnstep1, exOwnstep2,exOwnstep3, exOwnstep4 :: SNModel

exOwnstep0 = exampleLogicSection

exOwnstep1 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, a, ad, a]), (T 2, V.fromList [a, b, c, d])]
  dual' = M.fromList [(T 1, bDual), (T 2, sDual)]
  bDual = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDual = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.singleton (P 5)), (3, S.fromList [P 4, P 5])]

exOwnstep2 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, ab, cd, ad]), (T 2, V.fromList [a, b, cd, ad])]
  dual' = M.fromList [(T 1, bDual), (T 2, sDual)]
  bDual = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDual = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.singleton (P 5)), (3, S.fromList [P 4, P 5])]

exOwnstep3 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, ab, cd, ad]), (T 2, V.fromList [a, b, cd, ad])]
  dual' = M.fromList [(T 1, bDual), (T 2, sDual)]
  bDual = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 1, P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDual = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.fromList [P 4, P 5]), (3, S.fromList [P 4, P 5])]

exOwnstep4 = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, ab, acd, ad]), (T 2, V.fromList [a, b, acd, ad])]
  dual' = M.fromList [(T 1, bDual), (T 2, sDual)]
  bDual = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 1, P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDual = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.fromList [P 4, P 5]), (3, S.fromList [P 4, P 5])]




--TODO add testing for semantics apart from the updates!!! some
--TOOD add testing for case study


