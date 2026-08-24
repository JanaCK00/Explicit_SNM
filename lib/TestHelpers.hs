module TestHelpers where

import Syntax
import SNModel
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Semantics
import Test.QuickCheck
  (Property, classify, property, collect, forAll)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Vector as V
import Data.Set (Set)
import Data.IntSet (IntSet)
import CaseStudy (stabCountSafe)
import Types
import Test.QuickCheck.Gen
import GenerationUtils (isOfSizeBetween, randomPosMap)


propo1 :: Form
propo1 = Adopted 1 (P 1)


--Defines a simple tautology.
taut :: Form
taut = Disj [propo1, Neg propo1]


{-
Takes a double and determines a valid threshold using the following scheme:

tauOut = abs tauIn - floor(abs tauIn)
If tauIn is an odd integer, tauOut it 1 instead.

This is used so the arbitrary generation of Double can be used in tests.
-}

properTau :: Double -> Double
properTau tau
    | fracPart == 0 && odd intPart     = 1
    | otherwise                        = abs fracPart
  where
    (intPart, fracPart) = properFraction tau :: (Integer, Double)


--Checks if the dualVal doesn't map an agent to an empty set.
nonEmptyDualValmapping :: SNModel -> Bool
nonEmptyDualValmapping m = all noEmptyValue (dualVal m) where
  noEmptyValue = IntMap.foldr (\x acc -> x /= S.empty && acc) True

--Checks if the update operations don't produce a broken dualVal.
nonEmptyDualValmappingBasicInfl :: Double -> SNModel -> Bool
nonEmptyDualValmappingBasicInfl tau m = nonEmptyDualValmapping m' where
  tau'= properTau tau
  m' = updInflBasic tau' m

nonEmptyDualValmappingBasicSelec :: Double -> SNModel -> Bool
nonEmptyDualValmappingBasicSelec tau m = nonEmptyDualValmapping m' where
  tau'= properTau tau
  m' = updSelecBasic tau' m

nonEmptyDualValmappingVariantInfl :: Double -> SNModel -> Bool
nonEmptyDualValmappingVariantInfl tau m = nonEmptyDualValmapping m' where
  tau'= properTau tau
  m' = updInflVariant tau' m

nonEmptyDualValmappingVariantSelec :: Double -> SNModel -> Bool
nonEmptyDualValmappingVariantSelec tau m = nonEmptyDualValmapping m' where
  tau'= properTau tau
  m' = updSelecVariant tau' m


--Checks if the basic friendship selection update makes all relations reflexive.
selecMakesRefl :: SNModel -> Double -> Bool
selecMakesRefl m d1 = upM == makeReflModel upM where
    upM = updSelecBasic d1' m
    d1' = properTau d1

--Checks if the restricted friendship selection update makes all relations reflexive.
selecMakesReflVariant :: SNModel -> Double -> Bool
selecMakesReflVariant m d1 = upM == makeReflModel upM where
    upM = updSelecVariant d1' m
    d1' = properTau d1


--Checks if the basic friendship selection update makes all relations symmetric.
selecMakesSym :: SNModel -> Double -> Bool
selecMakesSym m d1 = updSelecBasic d1' m == makeSymModel (updSelecBasic d1' m) where
    d1' = properTau d1

--Counts how many iterations it takes for an Basic interleaving with constant tau to stabilize.
prop_numberOfTurns :: Double -> SNModel -> Property
prop_numberOfTurns tau m =
    let steps = snd $ stabCountSafe 100 (updInflBasic tau' . updSelecBasic tau') m
        tau' = properTau tau in
        collect steps $
        property True

--Counts how many iterations it takes for a Variant interleaving with constant tau to stabilize.
prop_numberOfTurnsVariant :: Double -> SNModel -> Property
prop_numberOfTurnsVariant tau m =
    let steps = snd $ stabCountSafe 20 (updInflVariant tau'. updSelecVariant tau') m
        tau' = properTau tau in
        collect steps $
        property True




{-
SECTION Syntax
-}

--Checks if a Form evaluates to the same as its simplified version on a given SNModel.
simplifyWorks :: SNModel -> Form -> Bool
simplifyWorks m f = (m |= f) == (m |= simplify f)


--Checks if a formula simplifies to Top or Bot.
isTrivial :: Form -> Bool
isTrivial f = f' == Top || f' == Bot where
    f' = simplify f


--Property to display the percentage of generated Forms that simplify to Top or Bot.
prop_trivialForm :: Form -> Property
prop_trivialForm f =
  classify (isTrivial f) "simplifies to Top/Bot" $
    property True

--Checks if a formula contains empty lists after Conj or Disj.
containsEmpty :: Form -> Bool
containsEmpty (Conj xs) = null xs || any containsEmpty xs
containsEmpty (Disj xs) = null xs || any containsEmpty xs
containsEmpty (Infl _ _ f) = containsEmpty f
containsEmpty (Selec _ _ f) = containsEmpty f
containsEmpty (Impl f g) = containsEmpty f || containsEmpty g
containsEmpty (Neg f) = containsEmpty f
containsEmpty _ = False

--Checks if a formula contains a list longer than 10 elements after Conj or Disj.
containsLongList :: Form -> Bool
containsLongList (Conj xs) = length xs > 10 || any containsLongList xs
containsLongList (Disj xs) = length xs > 10 || any containsLongList xs
containsLongList (Infl _ _ f) = containsLongList f
containsLongList (Selec _ _ f) = containsLongList f
containsLongList (Impl f g) = containsLongList f || containsLongList g
containsLongList (Neg f) = containsLongList f
containsLongList _ = False


--Checks if a simplified Form contains NO occurance of Top/Bot.
topBotFree :: Form -> Bool
topBotFree = allSubf freePred where
    freePred (Infl _ _ f)     = allSubf freePred f
    freePred (Selec _ _ f)    = allSubf freePred f
    freePred (Adopted _ _ ) = True
    freePred (Connected {}) = True
    freePred _ = False --Includes Top, Bot (plus for the sake of pattern exhaustion, all complex cases, but those should be handled by allSubf)

--Checks if every formula either simplifies to Top/Bot or simplifies to be free of any occurence of Top/Bot.
topBotpurity :: Form -> Bool
topBotpurity f = f' == Top || (f'== Bot || topBotFree f') where
    f' = simplify f


--Checks if for two consecutive Selecs, only the last applied matters.
consecutiveSelec :: SNModel -> Double -> Double -> Bool
consecutiveSelec m d1 d2 = updSelecBasic d1' m == updSelecBasic d1' (updSelecBasic d2' m) where
    d1' = properTau d1
    d2' = properTau d2


--Checks if an Infl Basic after a Selec Basic 1 doesn't change anything, except for Infl Basic 0.
consInflSelecOne :: SNModel -> Double  -> Bool
consInflSelecOne m d1 = (updSelecBasic 1 m == updInflBasic d1' (updSelecBasic 1 m)) || d1' == 0.0
    where d1' = properTau d1


--Checks if number of reachable agents never grows for Variant Selec.
noGrowingReachable :: Double -> SNModel -> Bool
noGrowingReachable tau m = reachUpdated `smallerEqualThan` reachOriginal where
    upM = updSelecVariant tau' m
    tau' = properTau tau
    transClosure rel' = makeReflexive $ makeTransitive $ combinedTopicsRel (nrAgents m) rel'
    reachOriginal = transClosure $ rel m
    reachUpdated = transClosure $ rel upM

--Checks if friends in rel1 is subset of friends in rel2 for all agents.
smallerEqualThan :: Relation -> Relation -> Bool
smallerEqualThan rel1 rel2 = (V.length rel1 == V.length rel2) && and (V.zipWith IntSet.isSubsetOf rel1 rel2)


--Checks if friendship selection with softer (=smaller) tau and then stronger (=bigger) tau leaves softer irrelevant.
variantSelecGrowingTau :: Double -> Double ->  SNModel -> Bool
variantSelecGrowingTau d1 d2 m | d1'<= d2' = updSelecVariant d2' (updSelecVariant d1' m) == updSelecVariant d2' m
                               | otherwise = variantSelecGrowingTau d2 d1 m
    where
    d1' = properTau d1
    d2' = properTau d2

--Checks if a Basic Infl doesn't change the relation.
inflNotChangeRel :: Double -> SNModel -> Bool
inflNotChangeRel tau m = rel m == rel m' where
    m' = updInflBasic tau' m
    tau' = properTau tau

--Checks if a Basic Selec doesn't change the dual valuation.
selecNotChangeDualVal :: Double -> SNModel -> Bool
selecNotChangeDualVal tau m = dualVal m == dualVal m' where
    m' = updSelecBasic tau' m
    tau' = properTau tau

--Checks if a Variant Infl doesn't change the relation.
inflVarNotChangeRel :: Double -> SNModel -> Bool
inflVarNotChangeRel tau m = rel m == rel m' where
    m' = updInflVariant tau' m
    tau' = properTau tau

--Checks if a Variant Selec doesn't change the dual valuation.
selecVarNotChangeDualVal :: Double -> SNModel -> Bool
selecVarNotChangeDualVal tau m = dualVal m == dualVal m' where
    m' = updSelecVariant tau' m
    tau' = properTau tau


--Checks if the function getRandomFormModel returns a well-formed form with the mode and matching the input SNModel.
wellFormedRandomFormModel :: SNModel -> Property
wellFormedRandomFormModel snm =
    forAll (elements [Basic, Variant]) $ \mode ->
    forAll (getRandomFormModel mode snm) $ \form ->
        isWellFormedForm form && match snm form && ((mode == Basic && isBasicCons form)|| (mode == Variant && isVariantCons form))

{-
SECTION
Hardcoded SNModels
-}

{-
(Example 2) from Smets et al. 2020  (all steps)
-}
exPaperstep0, exPaperstep1, exPaperstep2, exPaperstep3, exPaperstep4, exPaperstep5 :: SNModel
exPaperstep0 = examplePaper

exPaperstep1 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = V.fromList [IntSet.fromList [0..3], IntSet.fromList [0,1], IntSet.fromList [0,2,3], IntSet.fromList [0,2,3]]
  mRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.fromList [1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.singleton (P 2)), (2, S.fromList [P 1, P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDualVal = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 6, P 7]), (2, S.singleton (P 8)), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 12]), (3, S.fromList [P 9, P 10])]

exPaperstep2 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = V.fromList [IntSet.fromList [0..3], IntSet.fromList [0,1], IntSet.fromList [0,2,3], IntSet.fromList [0,2,3]]
  mRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.fromList [1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDualVal = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]

exPaperstep3 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = V.fromList [IntSet.fromList [0, 1, 2, 3], IntSet.fromList [0, 1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDualVal = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]

exPaperstep4 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = V.fromList [IntSet.fromList [0, 1, 2, 3], IntSet.fromList [0, 1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDualVal = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1, S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]

exPaperstep5 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = V.fromList [IntSet.fromList [0, 1, 3], IntSet.fromList [0, 1, 3], IntSet.singleton 2, IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDualVal = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1, S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5,P 8]), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 12])]


{-
(Example 4) with corrected typo from Smets et al. 2020  (all steps)
-}

exPaperVarstep0, exPaperVarstep1, exPaperVarstep2, exPaperVarstep3, exPaperVarstep4, exPaperVarstep5 :: SNModel
exPaperVarstep0 = examplePaper
exPaperVarstep1 = exPaperstep1


exPaperVarstep2 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = V.fromList [IntSet.fromList [0..3], IntSet.fromList [0,1], IntSet.fromList [0,2,3], IntSet.fromList [0,2,3]]
  mRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.fromList [1, 3], IntSet.fromList [0,2], IntSet.fromList [0,1,3]]
  sRel = V.fromList [IntSet.fromList [0, 2, 3], IntSet.singleton 1, IntSet.fromList [0,2, 3], IntSet.fromList [0,2,3]]
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDualVal = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.singleton (P 5)), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11]), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]


exPaperVarstep3 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = makeFullRel 4
  sRel = makeFullRel 4
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDualVal = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.singleton (P 5)), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11]), (2, S.fromList [P 9, P 10, P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]

exPaperVarstep4 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = makeFullRel 4
  sRel = makeFullRel 4
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDualVal = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5, P 6, P 7]), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11,  P 12]), (2, S.fromList [P 9, P 10, P 11,  P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]

exPaperVarstep5 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList [(T 1, fRel), (T 2, mRel), (T 3, sRel)]
  fRel = makeFullRel 4
  mRel = makeFullRel 4
  sRel = makeFullRel 4
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.fromList [P 2, P 3, P 4]), (2, S.fromList [P 2, P 3, P 4]), (3, S.fromList [P 2, P 3, P 4])]
  mDualVal = IntMap.fromList [(0, S.fromList [P 5, P 6, P 7]), (1,S.fromList [P 5, P 6, P 7]), (2, S.fromList [P 5, P 6, P 7]), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11,  P 12]), (1, S.fromList [P 9, P 10, P 11,  P 12]), (2, S.fromList [P 9, P 10, P 11,  P 12]), (3, S.fromList [P 9, P 10, P 11,  P 12])]

{-
Own example (interleaving of Variant Infl, Variant Selec)
-}



alice, bob, carol, david, emily :: Int
alice = 0
bob = 1
carol = 2
david = 3
emily = 4

books, games, sports :: Topic
books = T 1
games = T 2
sports = T 3


defaultTopics :: Set Topic
defaultTopics = S.fromList [books, games, sports]

fantasy, nonFiction, romance :: Position
fantasy = P 1
nonFiction = P 2
romance = P 3

booksPositions :: Set Position
booksPositions = S.fromList [fantasy, nonFiction, romance]

cardGames, boardGames, rolePlaying :: Position
cardGames = P 4
boardGames = P 5
rolePlaying = P 6

gamesPositions :: Set Position
gamesPositions = S.fromList [cardGames, boardGames, rolePlaying]

teamSports, endurance, weights :: Position
teamSports = P 7
endurance = P 8
weights = P 9

sportsPositions :: Set Position
sportsPositions = S.fromList [teamSports, endurance, weights]

a, b, c, d, ab, ac, bc, abc, ad, cd, acd :: IntSet
a = IntSet.singleton alice
b = IntSet.singleton bob
c = IntSet.singleton carol
ab = IntSet.fromList [alice, bob]
ac = IntSet.fromList [alice, carol]
bc = IntSet.fromList [bob, carol]
cd = IntSet.fromList [carol, david]
abc = IntSet.fromList [alice, bob, carol]
d = IntSet.singleton david
ad = IntSet.fromList [alice, david]
acd = IntSet.fromList [alice, carol, david]



exOwnstep0, exOwnstep1, exOwnstep2,exOwnstep3, exOwnstep4 :: SNModel

exOwnstep0 = exampleLogicSection

exOwnstep1 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, a, ad, a]), (T 2, V.fromList [a, b, c, d])]
  dualVal' = M.fromList [(T 1, bDualVal), (T 2, sDualVal)]
  bDualVal = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDualVal = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.singleton (P 5)), (3, S.fromList [P 4, P 5])]

exOwnstep2 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, ab, cd, ad]), (T 2, V.fromList [a, b, cd, ad])]
  dualVal' = M.fromList [(T 1, bDualVal), (T 2, sDualVal)]
  bDualVal = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDualVal = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.singleton (P 5)), (3, S.fromList [P 4, P 5])]

exOwnstep3 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, ab, cd, ad]), (T 2, V.fromList [a, b, cd, ad])]
  dualVal' = M.fromList [(T 1, bDualVal), (T 2, sDualVal)]
  bDualVal = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 1, P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDualVal = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.fromList [P 4, P 5]), (3, S.fromList [P 4, P 5])]

exOwnstep4 = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, ab, acd, ad]), (T 2, V.fromList [a, b, acd, ad])]
  dualVal' = M.fromList [(T 1, bDualVal), (T 2, sDualVal)]
  bDualVal = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.fromList [P 1, P 2]), (2, S.fromList [P 1, P 2, P 3]), (3, S.fromList [P 1,P 2,P 3])]
  sDualVal = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.fromList [P 4, P 5]), (3, S.fromList [P 4, P 5])]


examplePaper :: SNModel
examplePaper = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList $ zip (map T [1,2,3]) $ replicate 3 (makeEmptyRel 4)
  dualVal' = M.fromList [(T 1, fDualVal), (T 2, mDualVal), (T 3, sDualVal)]
  fDualVal = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.singleton (P 2)), (2, S.fromList [P 1, P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDualVal = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 6, P 7]), (2, S.singleton (P 8)), (3, S.fromList [P 5, P 6, P 7])]
  sDualVal = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 12]), (3, S.fromList [P 9, P 10])]

exampleLogicSection :: SNModel
exampleLogicSection = SNM 4 positions' rel' dualVal' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, a, ad, a]), (T 2, V.fromList [a, b, c, d])]
  dualVal' = M.fromList [(T 1, bDualVal), (T 2, sDualVal)]
  bDualVal = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.singleton (P 2)), (2, S.fromList [P 2, P 3]), (3, S.fromList [P 2,P 3])]
  sDualVal = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.fromList [P 5, P 6]), (3, S.singleton (P 5))]


--A small hardcoded example of an ill-formed SNModel.
snmWrong :: SNModel
snmWrong = SNM (-1) (M.fromList [(T 1, S.fromList [P 1]), (T 2, S.fromList [P 1, P 2])]) M.empty M.empty


--Checks if the function getRandomFormModel returns a well-formed SNModel.
wellFormedRandomSNModel :: Property
wellFormedRandomSNModel =
    forAll arbitraryWellFormedInput $ \(n, tps) ->
        forAll (getRandomSNModel n tps) $ \snm ->
            fst (isWellFormedSNModel snm)

--Generates an arbitrary well-formed input for getRandomSNModel.
arbitraryWellFormedInput :: Gen (Int, [(Topic, [Position])])
arbitraryWellFormedInput = do
    tpcs <- sublistOf (map T [1..nrTpcs]) `suchThat` (not . null)
    pos <- sublistOf (map P [1..nrPosTotal]) `suchThat` isOfSizeBetween (length tpcs) nrPosTotal
    n <- chooseInt (1, 100)
    randomTPMap <- randomPosMap tpcs pos
    let tps = M.toList $ M.map S.toList randomTPMap
    return (n, tps)


--TODO add testing for case study


