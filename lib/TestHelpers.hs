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


--test if an Infl after a Selec 1 doesn't change anything
consInflSelecOne :: SNModel -> Double  -> Bool
consInflSelecOne m d1 = (updSelecBasic 1 m == updInflBasic d1' (updSelecBasic 1 m)) || d1' == 0.0 --(order is not accrordning to syntax ;))
    where d1' = properTau d1
--TODO check more things I did in simplify


--check if an application of Selec makes all relations reflexive
selecMakesRefl :: SNModel -> Double -> Bool
selecMakesRefl m d1 = updSelecBasic d1' m == makeReflModel (updSelecBasic d1' m) where
    d1' = properTau d1


--check if an application of Selec makes all relations symmetric
selecMakesSym :: SNModel -> Double -> Bool
selecMakesSym m d1 = updSelecBasic d1' m == makeSymModel (updSelecBasic d1' m) where
    d1' = properTau d1


simplifyWorksBasic :: SNModel -> BasicForm -> Bool
simplifyWorksBasic m (BasicForm f) = simplifyWorks m f

simplifyWorksVariant :: SNModel -> VariantForm -> Bool
simplifyWorksVariant m (VariantForm f) = simplifyWorks m f

--checks if a Form evaluates to the same as its simplified version on a given SNModel
simplifyWorks :: SNModel -> Form -> Bool
simplifyWorks m f = (m |= f) == (m |= simplify f)


--TODO add these to ExplicitSpec
--check if the constrcucted full relation is symmetric and reflexive on some given SNModel

symAndRefl :: SNModel -> Bool
symAndRefl m = (makeFullRelModel m == makeReflModel (makeFullRelModel m)) && (makeFullRelModel m == makeSymModel (makeFullRelModel m))

isTrivialBasic :: BasicForm -> Bool
isTrivialBasic (BasicForm f) = isTrivial f

isTrivialVariant :: VariantForm -> Bool
isTrivialVariant (VariantForm f) = isTrivial f

--check if a formula simplifies to Top or Bot
isTrivial :: Form -> Bool
isTrivial f = f' == Top || f' == Bot where
    f' = simplify f


--TODO delete !.!
prop_trivialFormBasic :: BasicForm -> Property
prop_trivialFormBasic f =
  classify (isTrivialBasic f) "simplifies to Top/Bot" $
    property True

prop_trivialFormVariant :: VariantForm -> Property
prop_trivialFormVariant f =
  classify (isTrivialVariant f) "simplifies to Top/Bot" $
    property True

prop_numberOfTurns :: Double -> SNModel -> Property
prop_numberOfTurns tau m =
    let steps = snd $ fixCount ((updInflBasic tau'). (updSelecBasic tau')) m
        tau' = properTau tau in
        collect steps $
        property True

--check if a formula contains empty lists after Conj or Disj
containsEmptyBasic :: BasicForm -> Bool
containsEmptyBasic (BasicForm f) = containsEmpty f

containsEmptyVariant :: VariantForm -> Bool
containsEmptyVariant (VariantForm f) = containsEmpty f

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

--check if a simplified Form either simplifies to be trivial, or simplifies so it doesn't contain any occurances of Top/Bot
topBotpurityBasic :: BasicForm -> Bool
topBotpurityBasic (BasicForm f) = topBotpurity f

topBotpurityVariant :: VariantForm -> Bool
topBotpurityVariant (VariantForm f) = topBotpurity f


topBotpurity :: Form -> Bool
topBotpurity f = f' == Top || (f'== Bot || topBotFree f') where
    f' = simplify f



getFormBasic :: BasicForm -> Form
getFormBasic (BasicForm f) = f

getFormVariant :: VariantForm -> Form
getFormVariant (VariantForm f) = f

modeConsistentBas :: BasicForm -> Bool
modeConsistentBas (BasicForm f) = checkModeConsistent f

modeConsistentVar :: VariantForm -> Bool
modeConsistentVar (VariantForm f) = checkModeConsistent f


--CONTINUE HERE
--check if nr of reachable agents nerver grows for variant Selec
noGrowingReachable :: Double -> SNModel -> Bool
noGrowingReachable tau m = transClosure
    rel1 = rel m
    rel2 = rel upM
    upM = updSelecVariant tau m
    transClosure rel' = makeReflexive $ makeTransitive $ combinedTopicsRel rel'

--check if softer tau -> stronger tau leaves softer irrelevant
variantSelecGrowingTau :: Double -> Double ->  SNModel
variantSelecGrowingTau d1 d2 m | d1<= d2 = updSelecVariant d2' (updSelecVariant d1' m) = updSelecVariant d2' m
                               | otherwise = variantSelecGrowingTau d2 d1 m
    where
    d1' = properTau d1
    d2' = properTau d2

