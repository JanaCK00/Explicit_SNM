module Syntax where

import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sized
  , oneof
  , listOf
  , suchThat, elements
  )
import qualified Data.List as L (groupBy, sortOn, nub)
import SMCDEL.Internal.Help (lfp)
import SNModel
import GenerationUtils
import Test.QuickCheck.Gen (genDouble, chooseInt)
import Data.Containers.ListUtils (nubOrd)
import qualified Data.IntSet as IntSet
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Types



{-
This module defines the logical language.
It also provides formula simplification and random generation of formulas.
-}


--------------------------------------------------------------------------------
-- Formula definition
--------------------------------------------------------------------------------

{-
The two modes for the modal operators.
Basic: Operations as decribed under "Social Networks Dynamics" in Smets et al. (2020)
       (Social Influence and Friendship Selection)

Variant: Operations as described under "Variations" in Smets et al. (2020)
         (Extended Social Influence and Restricted Friendship Selection)
-}
data Mode = Basic | Variant deriving (Eq, Show, Ord)


{-
Syntax of Social Network Logic
A propositional language with two special atoms (Adopted and Connected) and four modal operators (parametrized by threshold):

(1) Infl Basic tau: Social Influence: Agents adopt positions per topic based on the proportion of
    friens in that topic that hold each position.
(2) Selec Basic tau: Friendship selection: Agents choose friends per topic among the set of all agents
    based on the proportion of positions they agree on.
(3) Infl Variant tau: Extended Social Influence: Agents adopt positions per topic based on the
    proportion of friens across all topics that hold each position.
(4) Selec Variant tau: Restricted Friendship selection: Agents choose friends per topic among all reachable
    agents (through any topic) based on the proportion of positions they agree on.


Forms are assumed to be at least in-update mode-consistent.
This means, we expect any Form not to contain both Infl Basic and Infl Variant,
as well as not to contain both Selec Basic and Selec Variant.
This is not enforced in construction but should be checked using the function isInUpdateModeCons.
-}
data Form
  = Top                         -- True Constant
  | Bot                         -- False Constant
  | Adopted Agent Position      -- Atom meaning "The agent has adopted the position."
  | Connected Topic Agent Agent -- Atom meaning "Agent1 considers Agent2 their friend on the topic." (directed)
  | Neg Form                    -- Negation
  | Conj [Form]                 -- Conjunction
  | Disj [Form]                 -- Disjunction
  | Impl Form Form              -- Implication (more efficient to implement as primitive (Gattinger (2018), p.90))
  | Infl Mode Double Form       -- Social influence (Basic or Variant) with threshold in [0,1]
  | Selec Mode Double Form      -- Friendship selection (Basic or Variant) with threshold in [0,1]
  deriving (Eq, Show, Ord)


{-
Some convenient abbreviations.
-}
-- Equivalence <->
equiv :: Form -> Form -> Form
equiv f g = Conj [Impl f g, Impl g f]

-- Exclusive OR
xor :: Form -> Form -> Form
xor f g = Disj [Conj [f, Neg g], Conj [Neg f, g]]


{-
Input:
List of operators (Infl mode tau or Selec mode tau (of type Form -> Form))
Form

Output:
Takes the given list of operators and prepends it to the given Form.
Returns resulting Form.
Example: operatorList [op1, op2, op3] f =  op1 ( op2 ( op3 f))

Important: This is not update application!
Semantically, the evaluation of the example output will be as follows for an SNModel m, where upd1 is the update corresponding to op1:
m |= op1 ( op2 ( op3 f))  <=>  upd1 m |= op2 ( op3 f)) <=> upd2 (upd1 m) |= op3 f  <=> upd3 (updp2 (upd1 m)) |= f
-}
operatorList :: [Form -> Form] -> Form -> Form
operatorList = flip (foldr ($))


--------------------------------------------------------------------------------
-- Predicates about modes in Form
--------------------------------------------------------------------------------

{-
Returns a tuple of Lists of Modes that occur in the Form.
(List of Modes found for Infl operator, List of Modes found for Selec operator)
-}
getModes :: Form -> ([Mode], [Mode])
getModes f = (L.nub $ getModeInfl f, L.nub $ getModeSelec f)


--Returns True if the Form is mode-consistent (all Infl and Selec have same mode).
isModeCons :: Form -> Bool
isModeCons f = isBasicCons f || isVariantCons f


--Returns True if all modal operators occuring in the Form are Mode Basic. False otherwise.
isBasicCons :: Form -> Bool
isBasicCons f = all (notElem Variant) [infls, selecs] where
  (infls, selecs) = getModes f

--Returns True if all modal operators occuring in the Form are Mode Variant. False otherwise.
isVariantCons :: Form -> Bool
isVariantCons f = all (notElem Basic) [infls, selecs] where
  (infls, selecs) = getModes f


-- Returns True if the Form is at least in-update mode-consistent. False otherwise.
isInUpdateModeCons :: Form -> Bool
isInUpdateModeCons f = consisInfl && consisSelec where
      (infls, selecs) = getModes f
      consisInfl = length infls < 2
      consisSelec  = length selecs < 2


{-
Returns a list of the found Infl modes.
(Returns [] if a form doesn't contain any Infl operators and is therefore mode un-specific.)
-}
getModeInfl :: Form -> [Mode]
getModeInfl (Infl mode _ f) = mode : getModeInfl f
getModeInfl (Selec _ _ f) = getModeInfl f
getModeInfl (Neg f) = getModeInfl f
getModeInfl (Conj xs) = concatMap getModeInfl xs
getModeInfl (Disj xs) = concatMap getModeInfl xs
getModeInfl (Impl f g) = getModeInfl f ++ getModeInfl g
getModeInfl _ = [] --includes Top, Bot, Adopted, Connected


{-
Returns a list of the found Selec modes.
(Returns [] if a form doesn't contain any Selec operators and is therefore mode un-specific.)
-}
getModeSelec :: Form -> [Mode]
getModeSelec (Infl _ _ f) = getModeSelec f
getModeSelec (Selec mode _ f) = mode : getModeSelec f
getModeSelec (Neg f) = getModeSelec f
getModeSelec (Conj xs) = concatMap getModeSelec xs
getModeSelec (Disj xs) = concatMap getModeSelec xs
getModeSelec (Impl f g) = getModeSelec f ++ getModeSelec g
getModeSelec _ = [] --includes Top, Bot, Adopted, Connected



--------------------------------------------------------------------------------
-- Some Form traversals that collect occurences of Agents, Topics and Positions.
-- Used in Semantics.hs to check if the occurences in a Form match an SNModel.
--------------------------------------------------------------------------------

-- Returns the Set of Agents that occur in the Form.
getAgs :: Form -> AgentSet
getAgs = IntSet.fromList . getAgsRec --Set creation takes care of duplicates.

getAgsRec :: Form -> [Agent]
getAgsRec (Adopted ag _) = [ag]
getAgsRec (Connected _ ag1 ag2) = [ag1, ag2]
getAgsRec (Neg f) = getAgsRec f
getAgsRec (Conj xs) = concatMap getAgsRec xs
getAgsRec (Disj xs) = concatMap getAgsRec xs
getAgsRec (Impl f g) = getAgsRec f ++ getAgsRec g
getAgsRec (Infl _ _ f) = getAgsRec f
getAgsRec (Selec _ _ f) = getAgsRec f
getAgsRec _ = [] --includes Top, Bot


-- Returns the Set of Topics that occur in the Form.
getTops :: Form -> Set Topic
getTops = S.fromList . getTopsRec  --Set creation takes care of duplicates.

getTopsRec :: Form -> [Topic]
getTopsRec (Connected t _ _) = [t]
getTopsRec (Neg f) = getTopsRec f
getTopsRec (Conj xs) = concatMap getTopsRec xs
getTopsRec (Disj xs) = concatMap getTopsRec xs
getTopsRec (Impl f g) = getTopsRec f ++ getTopsRec g
getTopsRec (Infl _ _ f) = getTopsRec f
getTopsRec (Selec _ _ f) = getTopsRec f
getTopsRec _ = [] --includes Top, Bot, Adopted



-- Returns the Set of Topics that occur in the Form.
getPos :: Form -> Set Position
getPos = S.fromList . getPosRec  --Set creation takes care of duplicates.

getPosRec :: Form -> [Position]
getPosRec (Adopted _ p) = [p]
getPosRec (Neg f) = getPosRec f
getPosRec (Conj xs) = concatMap getPosRec xs
getPosRec (Disj xs) = concatMap getPosRec xs
getPosRec (Impl f g) = getPosRec f ++ getPosRec g
getPosRec (Infl _ _ f) = getPosRec f
getPosRec (Selec _ _ f) = getPosRec f
getPosRec _ = [] --includes Top, Bot, Connected



--------------------------------------------------------------------------------
-- Simplification of Form
--------------------------------------------------------------------------------

{-
Simplifies a formula to an equivalent formula.
Adapted from Symbolic-Topo-E-Models.Syntax. (dos Santons Gomes (2025))

! ASSUMES: in-update mode-consistency
-}
simplify :: Form -> Form
simplify = lfp simStep    --lfp keeps applying simStep until the result is constant.

simStep :: Form -> Form
simStep Top             = Top
simStep Bot             = Bot
simStep (Connected t a1 a2) = Connected t a1 a2
simStep (Adopted ag p)  = Adopted ag p
simStep (Neg Top)       = Bot
simStep (Neg Bot)       = Top
simStep (Neg (Neg f))   = simStep f
simStep (Neg (Infl mode tau f))   = simStep (Infl mode tau (Neg f))  --Bubble up modal operator. Follows from recursion axioms.
simStep (Neg (Selec mode tau f )) = simStep (Selec mode tau (Neg f)) --Bubble up modal operator. Follows from recursion axioms.
simStep (Neg f)         = Neg $ simStep f
simStep (Conj [])       = Top
simStep (Conj [f])      = simStep f
simStep (Conj fs)      | Bot `elem` fs                    = Bot
                       | or [ Neg f `elem` fs | f <- fs ] = Bot
                       | otherwise                        = groupByOperator $ Conj (nubOrd $ concatMap unpack fs) where
                        {-
                         groupByOperator bubbles up modal operators that are shared by more than one element in the list.
                        -}
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
                          {-
                           Unpack takes care of nested Conj. Example: unpack (Conj [f1, Conj [f2, f3]]) = Conj [f1, f2, f3]
                          -}
simStep (Disj [])       = Bot
simStep (Disj [f])      = simStep f
simStep (Disj fs)      | Top `elem` fs                    = Top
                       | or [ Neg f `elem` fs | f <- fs ] = Top
                       | otherwise                        = groupByOperator $ Disj (nubOrd $ concatMap unpack fs) where
                          unpack Bot = []
                          unpack (Disj subfs) = map simStep $ filter (Bot /=) subfs
                          unpack f = [simStep f]
simStep (Impl Bot _)    = Top
simStep (Impl _ Top)    = Top
simStep (Impl Top f)    = simStep f
simStep (Impl f Bot)    = Neg (simStep f)

{-
Bubble up modal operator, if it's the same on both sides of the implication.
Follows from recursion axioms.
  -}
simStep (Impl f@(Infl mode1 tau1 subF) g@(Infl _ tau2 subG)) | tau1==tau2  = Infl mode1 tau1 (simStep (Impl subF subG)) --assumes in-update mode-consistency
                                                             | otherwise   = Impl (simStep f) (simStep g)
simStep (Impl f@(Selec mode1 tau1 subF) g@(Selec _ tau2 subG)) | tau1==tau2  = Selec mode1 tau1 (simStep (Impl subF subG)) --assumes in-update mode-consistency
                                                               | otherwise   = Impl (simStep f) (simStep g)
simStep (Impl f g)     | f==g      = Top
                       | otherwise = Impl (simStep f) (simStep g)

{-
Eliminate modal operators on Bot or Top. Follows from recursion axioms.
-}
simStep (Infl _ _ Bot)  = Bot
simStep (Infl _ _ Top)  = Top
simStep (Selec _ _ Bot) = Bot
simStep (Selec _ _ Top) = Top

{-
Selec Basic:
(1) Selec Basic does not impact the valuation.
    Selec Basic solely depends on valuation (not on relation).
    It follows, that two Selec Basic in a row leave the first applied irrelevant.
    Therefore, if we only check a boolean combination of Adopted and Selec Basic, (no Infl, no Connected)
    we can eliminate the outer Selec Basic.
(2) Selec Basic 1 connects only agents that hold the same set of positions per topic.
    Infl Basic will therefore not change anything. (except Infl Basic 0, which is handled in removeLeadingInflBasic).
    We therefore remove all Infl Basic with tau > 0 that follow a Selec Basic 1.

Selec Varinat:
(1) Selec Variant does not impact the valuation.
    Twp Selec Variant in a row with increasing or constant tau leave the first applied irrelevant.
    Therefore, if we only check a boolean combination of Adopted and stricter/equal Selec Variant (no softer Selec Variant, no Connected),
    we can eliminate the outer Selec Variant.
-}
simStep (Selec mode tau f) | mode == Basic && madeOfAdopSelec f              = simStep f
                           | mode == Variant && madeOfAdopStrictSelec tau f  = simStep f
                           | mode == Basic && tau==1                         = Selec Basic tau (simStep (removeLeadingInflBasic f))
                           | otherwise                                       = Selec mode tau (simStep f)


{-
Infl _ does not impact the relation.
Therefore, if we only check a boolean combination of Connected,
we can eliminate the Infl _.
-}
simStep (Infl mode tau f) | boolOfConnected f = simStep f
                          | otherwise         = Infl mode tau (simStep f)


--------------------------------------------------------------------------------
-- Helper functions for simStep
--------------------------------------------------------------------------------

{-
Input:
Predicate
Form

Output:
Folds a Form on its subformulas using the provided predicate.
(!Formula inside an Update does NOT count as a subformula.)
-}
allSubf :: (Form -> Bool) -> Form -> Bool
allSubf predi (Neg f)      = allSubf predi f
allSubf predi (Conj xs)    = all (allSubf predi) xs
allSubf predi (Disj xs)    = all (allSubf predi) xs
allSubf predi (Impl f1 f2) = allSubf predi f1 && allSubf predi f2
allSubf predi f            = predi f -- includes Top, Bot, PrpF, Update



{-
Input:
Form

Output:
Checks if the Form is a boolean combination of Connected Propositions. (or Top/Bot)
-}

boolOfConnected :: Form -> Bool
boolOfConnected = allSubf connectedPred where
  connectedPred (Adopted _ _)         = False
  connectedPred (Infl {})             = False
  connectedPred (Selec {})            = False
  connectedPred _                     = True --includes Top, Bot, PrpF Connected (plus for the sake of pattern exhaustion all the complex constructors)


{-
Input:
Form

Output:
Checks if a given formula is a boolean combination of Adopted Propositions. (or Top/Bot)
-}
boolOfAdopted :: Form -> Bool
boolOfAdopted = allSubf adoptedPred where
  adoptedPred (Connected {})        = False
  adoptedPred (Infl {})             = False
  adoptedPred (Selec {})            = False
  adoptedPred _                     = True --includes Top, Bot, PrpF Adopted (plus for the sake of pattern exhaustion all the complex constructors)


{-
Input:
Form

Output:
Checks if a formula has all it's subformulas starting with a Selec,
or is Top and Bot or a PrpF Adopted.
-}
madeOfAdopSelec :: Form -> Bool
madeOfAdopSelec = allSubf selecAdopPred where
  selecAdopPred (Infl {})            = False
  selecAdopPred (Connected {})       = False
  selecAdopPred _                    = True --includes Top, Bot, Update Selec, PrpF Adopted (plus for the sake of pattern exhaustion all the complex constructors)


{-
Input:
Threshold tau
Form

Output:
Checks if a formula has all it's subformulas starting with a Selec stricter or equal to tau,
or is Top and Bot or a PrpF Adopted.
-}
madeOfAdopStrictSelec :: Double -> Form -> Bool
madeOfAdopStrictSelec tau = allSubf (selecStrictAdopPred tau) where
  selecStrictAdopPred _ (Infl {})            = False
  selecStrictAdopPred _ (Connected {})       = False
  selecStrictAdopPred tau1 (Selec _ tau2 _) = tau2 >= tau1
  selecStrictAdopPred _ _                    = True --includes Top, Bot, PrpF Adopted (plus for the sake of pattern exhaustion all the complex constructors)



{-
Input:
Form (only used for Forms of type Conj or Disj)

Output:
Groups the list according to leading modal operator.
Formulas that don't start with a modal operator are grouped together.
Then, the common modal operator per group is bubbled up.
For Conj [] or Disj [], nothing happens.
-}
groupByOperator :: Form -> Form
groupByOperator (Conj xs) = Conj (concatMap (bubbleUpOp Conj) (L.groupBy hasSameOp (L.sortOn operator xs))) --if this is a singleton list, it will be simplified in the next round
groupByOperator (Disj xs) = Disj (concatMap (bubbleUpOp Disj) (L.groupBy hasSameOp (L.sortOn operator xs)))
groupByOperator f         = f --only here for pattern exhaustion


{-
Input:
Form (only used for Forms of type Infl or Selec)

Output:
Returns the leading modal operator (for the sake of comparability (can't compare functions), completed to a Form),
if present.
-}

operator :: Form -> Maybe Form
operator (Infl mode tau _)   = Just (Infl mode tau Top)
operator (Selec mode tau _)  = Just (Selec mode tau Top)
operator _                   = Nothing

{-
Input:
Two modal operators (completed to a Form)

Output:
Returns a Bool indicating if the two Forms start with the same modal operator.
(Returns True if both do not start with an update at all.)
-}
hasSameOp :: Form -> Form -> Bool
hasSameOp f1 f2 = operator f1 == operator f2

{-
Input:
Constructor of Form (Conj or Disj)
A list of Forms that start with the same modal operator.
(Or: they all don't start with an modal operator.)

Output:
Bubbles up the shared modal operator.

Example:
bubbleUpOp Conj [Infl Basic 0.5 f, Infl Basic 0.5 g] = [Infl Basic 0.5 (Conj [f, g])]
-}
bubbleUpOp :: ([Form] -> Form) -> [Form] -> [Form]
bubbleUpOp _ [x]                           = [x] --do nothing, if is a singleton list
bubbleUpOp constr ((Infl mode tau x):xs)   = [Infl mode tau (removeFirstOp (constr (x:xs)))]
bubbleUpOp constr ((Selec mode tau x):xs)  = [Selec mode tau (removeFirstOp (constr (x:xs)))]
bubbleUpOp _ xs                            = xs    --list of formulas that don't start with a modal operator (incl. the empty list)


{-
Input:
Form

Output:
Removes the first modal operator of all subformulas in Conj/Disj.
Intended only to be used for Forms of type Conj or Disj with lists of Forms starting with modal operator.
-}
removeFirstOp :: Form -> Form
removeFirstOp (Infl _ _ f)   = f
removeFirstOp (Selec _ _ f)  = f
removeFirstOp (Conj xs)    = Conj (map removeFirstOp xs)
removeFirstOp (Disj xs)    = Disj (map removeFirstOp xs)
removeFirstOp g            = g --includes Top/Bot. Otherwise only here for pattern exhaustion.


{-
Intended only for in-update mode-consistent Forms.

Input:
Form

Output:
Removes all Infl Basic until either a Selec, an Infl Variant or an Infl Basic 0 is reached.
-}

removeLeadingInflBasic :: Form -> Form
removeLeadingInflBasic  (Infl Basic tau f)  | tau == 0 = Infl Basic 0 (removeLeadingInflBasic f)
                                            | otherwise = removeLeadingInflBasic  f
removeLeadingInflBasic  (Impl f1 f2)  = Impl (removeLeadingInflBasic  f1) (removeLeadingInflBasic  f2)
removeLeadingInflBasic  (Conj xs)     = Conj $ map removeLeadingInflBasic  xs
removeLeadingInflBasic  (Disj xs)     = Disj $ map removeLeadingInflBasic  xs
removeLeadingInflBasic  (Neg f)       = Neg $ removeLeadingInflBasic  f
removeLeadingInflBasic  f             = f -- includes Top, Bot, PrpF, Selec _ and Infl Variant




--------------------------------------------------------------------------------
-- Random generation of Form
--------------------------------------------------------------------------------

{-
Input:
mode: Mode that all modal operators will use
snm: SNModel

Output:
Returns a randomly generated, mode-consistent and simplified Form that matches the provided SNModel.
This means, all Agents, Topics and Positions that occur in the random Form are present in the SNModel.
Hence, the Form can be checked on the SNModel.

Example input in ghci:
import Test.QuickCheck
myModel = ...
myForm <- generate (getRandomForm Basic myModel)
-}
getRandomFormModel :: Mode -> SNModel -> Gen Form
getRandomFormModel mode snm = do
  let ags = nrAgents snm
  let posList =  M.toList $ M.map S.toList $ positions snm
  getRandomForm mode ags posList


{-
Input:
mode: Mode that all modal operators will use
n: number of agents
tps: list of tuples (Topic, [Position])

Output:
Returns a randomly generated, mode-consistent and simplified Form that matches the input.
This means, all Agents, Topics and Positions that occur in the random Form were part of the input.

Example input in ghci:
import Test.QuickCheck
myForm <- generate (getRandomForm Basic 5 [(T 1,[P 1, P 2]), (T 2, [P 3, P 4])])
-}
getRandomForm :: Mode -> Int -> [(Topic, [Position])] -> Gen Form
getRandomForm mode n tps = simplify <$> randomForm arbA arbT arbP mode mode 10 --last parameter is a fixed, humanly readable size
  where arbA = chooseInt (0, n-1)
        arbT = elements $ map fst tps
        arbP = elements $ concatMap snd tps

{-
Adapted from Symbolic-Topo-E-Models.Syntax.

Input:
arbA: A generator for random Int
arbT: A generator for random Topic
arbP: A generator for random Position
i: Mode for Infl
s: Mode for Selec
n: size (is decreasing to make sure we stop the recursive generation)

Output:
Generates a random Form that is at least in-update mode-consistent.
If the both provided modes are equal, the random Form will be mode-consistent.

 To avoid a high percentage of generated formulas simplifying to Top/Bot, the random generation:
  - doesn't include pure Top/Bot
  - avoids empty list for Conj/Disj
Like this less than 30% of generated formulas evaluate to Top/Bot.
-}
randomForm :: Gen Int -> Gen Topic -> Gen Position -> Mode -> Mode -> Int -> Gen Form
randomForm arbA arbT arbP _ _ 0 = oneof [ Adopted <$> arbA <*> arbP
                    , Connected <$> arbT <*> arbA <*> arbA
                    ]
randomForm arbA arbT arbP i s n = oneof [ Adopted <$> arbA <*> arbP
                    , Connected <$> arbT <*> arbA <*> arbA
                    , Neg <$> st
                    , Conj <$> listOf st `suchThat` isOfSizeBetween 1 10 --restricts the list to a maximum of 10 elements
                    , Disj <$> listOf st `suchThat` isOfSizeBetween 1 10
                    , Impl <$> st <*> st
                    , Infl i <$> genDouble <*> st
                             , Selec s <$> genDouble <*> st
                    ]
    where
      st = randomForm arbA arbT arbP i s (n `div` 3)

{-
Generates arbitrary sized formulas based on the defined default values in SNModel.hs.
The default values ensure that the arbitrary formulas match the arbitrary SNModels.
This means, all Agents, Topics and Positions that occur in an arbitrary Form occur in any arbitrary SNModel.
The formulas are mode-consistent.
-}

instance Arbitrary Form where
    arbitrary = do
      mode <- elements [Basic, Variant] --can be changed, if we want to allow mixed-mode (but in-update consistent) formulas
      sized (randomForm arbADef arbTDef arbPDef mode mode) where
        arbADef = chooseInt (0, defaultNrAgs-1)
        arbTDef = T <$> chooseInt (1, nrTpcs)
        arbPDef = P <$> chooseInt (1, nrPosTotal)


{-
usage in ghci:
import Test.QuickCheck
myForm <- generate arbitrary :: IO Form --(default sized passed is 30)
myForm <- generate (resize 10 arbitrary) :: IO Form --to change the size
isInUpdateModeCons myForm
simplify myForm
-}

