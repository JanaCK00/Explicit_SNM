module Syntax where


--TODO do only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sized
  , oneof
  , listOf
  , suchThat
  )
import qualified Data.List as L (groupBy, sortOn, nub)
import SMCDEL.Internal.Help (lfp)
import SNModel
import SetTheory
import Test.QuickCheck.Gen (genDouble, chooseInt)
import Data.Containers.ListUtils (nubOrd)

{-
  Language, simplification of formulas, arbitrary generation of formulas.
-}



{-
Syntax of Social Network Logic (propositional language with
the special atoms Adopted and Connected, and the dynamic operators Infl (Social Influence)
and Selec (Friendship Selection)
-}


--used to define mode of updates
data Mode = Basic | Variant deriving (Eq, Show, Ord)


--in the following I assume a Form is mode-consistent (= all Infl/Selec are of same mode)
data Form
  = Top
  | Bot
  | Adopted Agent Position -- atom meaning "The agent has adopted the position."
  | Connected Topic Agent Agent -- atom meaning "Agent1 considers Agent2 their friend on the topic."
  | Neg Form
  | Conj [Form]
  | Disj [Form]
  | Impl Form Form -- faster as primitive (quote Gattinger)
  | Infl Mode Double Form -- Social influence: Agents change positions based on their topic-specific network, acc to threshold.
  | Selec Mode Double Form -- Friendship selection: Agents choose social connections per topic based on the proportion of positions they agree on, acc to threshold.
  deriving (Eq, Show, Ord)


--return True if a Form doesn't contain both Modes, False otherwise
checkModeConsistent :: Form -> Bool
checkModeConsistent f = length (L.nub $ getMode f) < 2

--returns a list of all found modes, returns [] if a form doesn't contain any updates and is therefore mode un-specific
getMode :: Form -> [Mode]
getMode (Infl mode _ _) = [mode]
getMode (Selec mode _ _) = [mode]
getMode (Neg f) = getMode f
getMode (Conj xs) = concatMap getMode xs
getMode (Disj xs) = concatMap getMode xs
getMode (Impl f g) = getMode f ++ getMode g
getMode _ = [] --includes Top, Bot, Adopted, Connected


--Abbreviations

--TODO are these even needed?
--TODO ? change these to primitives (quote Gattinger, p. 90)
--TODO more abbreviations?

--equivalence <->
equiv :: Form -> Form -> Form
equiv f g = Conj [Impl f g, Impl g f]

--XOR
xor :: Form -> Form -> Form
xor f g = Disj [Conj [f, Neg g], Conj [Neg f, g]]



{-
Translate sequence of updates (Infl mode tau or Selec mode tau (of type Form -> Form)) to formula.
Different tau are allowed, mode-consistency is assumed (but not enforced)
Example: updateSeq [up1, up2, up3] f =  up1 ( up2 ( up3 f))
-}
updateSeq :: [Form -> Form] -> Form -> Form
updateSeq = flip (foldr ($))

{-
Simplify a formula to an equivalent formula.
Adapted from Symbolic-Topo-E-Models.Syntax.

! ASSUMES: mode-consistent Form
TODO if I want only in-update mode-consistence, I have to change in one case (Selec 1)
-}
simplify :: Form -> Form
simplify = lfp simStep    --lfp keeps applying simStep until the result is constant.

simStep :: Form -> Form
simStep Top             = Top
simStep Bot             = Bot
simStep (Connected t a1 a2) = Connected t a1 a2
simStep (Adopted ag p)   = Adopted ag p
simStep (Neg Top)       = Bot
simStep (Neg Bot)       = Top
simStep (Neg (Neg f))   = simStep f
simStep (Neg (Infl mode tau f)) = simStep (Infl mode tau (Neg f)) --bubble up update operator
simStep (Neg (Selec mode tau f )) = simStep (Selec mode tau (Neg f)) --bubble up update operator
simStep (Neg f)         = Neg $ simStep f
simStep (Conj [])       = Top
simStep (Conj [f])      = simStep f
simStep (Conj fs)      | Bot `elem` fs                    = Bot
                       | or [ Neg f `elem` fs | f <- fs ] = Bot
                       | otherwise                        = groupByOperator $ Conj (nubOrd $ concatMap unpack fs) where
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
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
--bubble up update operator if it's the same on both sides of implication
simStep (Impl f@(Infl mode1 tau1 subF) g@(Infl _ tau2 subG)) | tau1==tau2  = Infl mode1 tau1 (simStep (Impl subF subG)) --assume mode-consistent
                                                             | otherwise   = Impl (simStep f) (simStep g)
simStep (Impl f@(Selec mode1 tau1 subF) g@(Selec _ tau2 subG)) | tau1==tau2  = Selec mode1 tau1 (simStep (Impl subF subG)) --assume mode-consistent
                                                               | otherwise   = Impl (simStep f) (simStep g)
simStep (Impl f g)     | f==g      = Top
                       | otherwise = Impl (simStep f) (simStep g)
simStep (Infl _ _ Bot)  = Bot
simStep (Infl _ _ Top)  = Top
simStep (Selec _ _ Bot) = Bot
simStep (Selec _ _ Top) = Top

{-
Basic:
(1) Update Selec does not impact positions + two Selecs in a row (not matter the tau) leave the first applied irrelevant
      Therefore if we only check a boolean combination of Adopted propositions and Selecs, (no Infl, no Connected)
      we can skip computing the outer Selec.
(2) After Selec 1, influence won't change anything (except Infl 0, which is handled in removeLeadingInfl).

Variant:
(1) Update Selec does not impact positions + two Selecs in a row with increasing or constant tau leave the first applied irrelevant.
  Therefore if we only check a boolean combination of Adopted propositions and stricter/equal Selecs (no softer Selecs, no Connected),
  we can skip computing the update.
TODO CHECK IF THE PART ABOUT SELECS IS CORRECT

-}
simStep (Selec mode tau f) | mode == Basic && madeOfAdopSelec f              = simStep f
                           | mode == Variant && madeOfAdopStrictSelec tau f  = simStep f
                           | mode == Basic && tau==1                         = Selec Basic tau (simStep (removeLeadingInfl f)) --TODO assumes mode-consistent across Selec/Infl!
                           | otherwise                                       = Selec mode tau (simStep f)


{-
Update Infl does not impact connections.
Therefore, if we only check a boolean combination of Connected propositions,
  we can skip computing the update.
-}
simStep (Infl mode tau f) | boolOfConnected f = simStep f
                          | otherwise         = Infl mode tau (simStep f)


{-
Basically folds a Form on it's subformulas using the provided predicate.
(ACHTUNG Formula inside an Update does NOT count as a subformula)
-}
allSubf :: (Form -> Bool) -> Form -> Bool
allSubf predi (Neg f)      = allSubf predi f
allSubf predi (Conj xs)    = all (allSubf predi) xs
allSubf predi (Disj xs)    = all (allSubf predi) xs
allSubf predi (Impl f1 f2) = allSubf predi f1 && allSubf predi f2
allSubf predi f            = predi f -- includes Top, Bot, PrpF, Update

{-
TODO needed??

--basically maps a function over all subformulas (ACHTUNG Formula inside an Update does NOT count as a subformula)
mapSubf :: (Form -> Form) -> Form -> Form
mapSubf g (Neg f)      = Neg $ mapSubf g f
mapSubf g (Conj xs)    = Conj $ map (mapSubf g) xs
mapSubf g (Disj xs)    = Disj $ map (mapSubf g) xs
mapSubf g (Impl f1 f2) = Impl (mapSubf g f1) (mapSubf g f2)
mapSubf g f            = g f --Inludes Top, Bot, PrpF, Update
-}


--Checks if a given formula is a boolean combination of Connected Propositions. (or Top/Bot)
boolOfConnected :: Form -> Bool
boolOfConnected = allSubf connectedPred where
  connectedPred (Adopted _ _)         = False
  connectedPred (Infl {})             = False
  connectedPred (Selec {})            = False
  connectedPred _                     = True --includes Top, Bot, PrpF Connected (plus for the sake of pattern exhaustion all the complex constructors)


--TODO maybe delete if not used
--Checks if a given formula is a boolean combination of Connected Propositions. (or Top/Bot)
boolOfAdopted :: Form -> Bool
boolOfAdopted = allSubf adoptedPred where
  adoptedPred (Connected {})        = False
  adoptedPred (Infl {})             = False
  adoptedPred (Selec {})            = False
  adoptedPred _                     = True --includes Top, Bot, PrpF Adopted (plus for the sake of pattern exhaustion all the complex constructors)


{-
Checks if a formula has all it's subformulas starting with a Selec, or is Top and Bot
  (where the update is also irrelevant), or a PrpF Adopted.
-}
madeOfAdopSelec :: Form -> Bool
madeOfAdopSelec = allSubf selecAdopPred where
  selecAdopPred (Infl {})            = False
  selecAdopPred (Connected {})       = False
  selecAdopPred _                    = True --includes Top, Bot, Update Selec, PrpF Adopted (plus for the sake of pattern exhaustion all the complex constructors)


{-
Checks if a formula has all it's subformulas starting with a Selec stricter or equal to provided tau, or is Top and Bot
  (where the update is also irrelevant), or a PrpF Adopted.
-}
madeOfAdopStrictSelec :: Double -> Form -> Bool
madeOfAdopStrictSelec tau = allSubf (selecStrictAdopPred tau) where
  selecStrictAdopPred _ (Infl {})            = False
  selecStrictAdopPred _ (Connected {})       = False
  selecStrictAdopPred tau1 (Selec _ tau2 _) = tau2 >= tau1
  selecStrictAdopPred _ _                    = True --includes Top, Bot, PrpF Adopted (plus for the sake of pattern exhaustion all the complex constructors)



{-
Takes a list-Formula (Conj or Disj) and groups said list according to leading Update operator.
Formulas that don't start with an update operator are grouped together. Then, the common update operator
is bubbled up.
For Conj [] or Disj [], nothing happends.
-}
groupByOperator :: Form -> Form
groupByOperator (Conj xs) = Conj (concatMap (bubbleUpOp Conj) (L.groupBy hasSameOp (L.sortOn operator xs))) --if this is a singleton list, it will be simplified in the next round
groupByOperator (Disj xs) = Disj (concatMap (bubbleUpOp Disj) (L.groupBy hasSameOp (L.sortOn operator xs)))
groupByOperator f         = f --only here for pattern exhaustion


--Return the leading update operator (for the sake of comparability (can't compare functions), completed to a Form), if present.
operator :: Form -> Maybe Form
operator (Infl mode tau _)   = Just (Infl mode tau Top)
operator (Selec mode tau _)  = Just (Selec mode tau Top)
operator _                   = Nothing

{-
Return a Bool indicating if two formulas start with the same update operator.
Returns True if both do not start with an update at all.
-}
hasSameOp :: Form -> Form -> Bool
hasSameOp f1 f2 = operator f1 == operator f2

{-
The first argument is a constructur of Form (Conj or Disj).
The second argument a list of Forms that start with the same update operator.
  or: they all don't start with an update operator at all.
It will bubble up that shared Update operator.
-}
bubbleUpOp :: ([Form] -> Form) -> [Form] -> [Form]
bubbleUpOp _ [x]                      = [x] --do nothing, if is a singleton list
bubbleUpOp constr ((Infl mode tau x):xs)   = [Infl mode tau (removeFirstOp (constr (x:xs)))]
bubbleUpOp constr ((Selec mode tau x):xs)  = [Selec mode tau (removeFirstOp (constr (x:xs)))]
bubbleUpOp _ xs                       = xs    --list of stuff that doesn't start with an Update Operator (incl the empty list)


{-
Removes the first update operator of all subformulas in Conj/Disj.
Intended only to be used for Forms that are lists of forms that start with update operator
-}
removeFirstOp :: Form -> Form
removeFirstOp (Infl _ _ f)   = f
removeFirstOp (Selec _ _ f)  = f
removeFirstOp (Conj xs)    = Conj (map removeFirstOp xs)
removeFirstOp (Disj xs)    = Disj (map removeFirstOp xs)
removeFirstOp g            = g --includes Top/Bot. Otherwise only here for pattern exhaustion.

--Removes all Infl Updates until a Selec is reached. Exception: Infl 0 not removed and stops the chain.
--should only be called for Forms of Mode Basic
removeLeadingInfl :: Form -> Form
removeLeadingInfl (Infl mode tau f)  | tau == 0 = Infl mode 0 f
                                     | otherwise = removeLeadingInfl f
removeLeadingInfl (Impl f1 f2)  = Impl (removeLeadingInfl f1) (removeLeadingInfl f2)
removeLeadingInfl (Conj xs)     = Conj $ map removeLeadingInfl xs
removeLeadingInfl (Disj xs)     = Disj $ map removeLeadingInfl xs
removeLeadingInfl (Neg f)       = Neg $ removeLeadingInfl f
removeLeadingInfl f             = f -- includes Top, Bot, PrpF, and most importantly Update Selec


{-
  Generate arbitrary sized formulas.
  Adapted from Symbolic-Topo-E-Models.Syntax.

  To avoid a high percentage of generated formulas simplifying to Top/Bot, the random generation:
    - doesn't include pure Top/Bot
    - avoids empty list for Conj/Disj
  LIke this less than 30% of generated formulas evaluate to Top/Bot.


  We distinguish between Forms of Mode Basic and Forms of Mode Variant.
-}

newtype BasicForm = BasicForm Form deriving (Eq, Ord, Show)
newtype VariantForm = VariantForm Form deriving (Eq, Ord, Show)


instance Arbitrary BasicForm where
    arbitrary = sized randomBasicForm
      where

        arbitraryAg = chooseInt (0, defaultNrAgs-1)
        arbitraryPos = P <$> chooseInt (1, nrPosTotal)
        arbitraryTpc = T <$> chooseInt (1, nrTpcs)

        randomBasicForm :: Int -> Gen BasicForm
        randomBasicForm i = BasicForm <$> randomForm i
        randomForm 0 = oneof [ Adopted <$> arbitraryAg <*> arbitraryPos
                             , Connected <$> arbitraryTpc <*> arbitraryAg <*> arbitraryAg
                             ]
        randomForm n = oneof [ Adopted <$> arbitraryAg <*> arbitraryPos
                             , Connected <$> arbitraryTpc <*> arbitraryAg <*> arbitraryAg
                             , Neg <$> st
                             , Conj <$> listOf st `suchThat` (not . null)
                             , Disj <$> listOf st `suchThat` (not . null)
                             , Impl <$> st <*> st
                             , Infl Basic <$> genDouble <*> st
                             , Selec Basic <$> genDouble <*> st
                             ]
          where
            st = randomForm (n `div` 3)



instance Arbitrary VariantForm where
    arbitrary = sized randomVariantForm
      where

        arbitraryAg = chooseInt (0, defaultNrAgs-1)
        arbitraryPos = P <$> chooseInt (1, nrPosTotal)
        arbitraryTpc = T <$> chooseInt (1, nrTpcs)

        randomVariantForm :: Int -> Gen VariantForm
        randomVariantForm i = VariantForm <$> randomForm i
        randomForm 0 = oneof [ Adopted <$> arbitraryAg <*> arbitraryPos
                             , Connected <$> arbitraryTpc <*> arbitraryAg <*> arbitraryAg
                             ]
        randomForm n = oneof [ Adopted <$> arbitraryAg <*> arbitraryPos
                             , Connected <$> arbitraryTpc <*> arbitraryAg <*> arbitraryAg
                             , Neg <$> st
                             , Conj <$> listOf st `suchThat` (not . null)
                             , Disj <$> listOf st `suchThat` (not . null)
                             , Impl <$> st <*> st
                             , Infl Variant <$> genDouble <*> st
                             , Selec Variant <$> genDouble <*> st
                             ]
          where
            st = randomForm (n `div` 3)

--TODO add generation of mixed mode formulas?

--TODO add shrink?? (maybe after I'm done with simplify and am sure it works...) see gattinger

{-
usage in ghci:
import Test.QuickCheck
myForm <- generate arbitrary :: IO Form --(default sized passed is 30)
simplify myForm
-}
