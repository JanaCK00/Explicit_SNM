module Syntax where


--TODO do only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sized
  , oneof
  , listOf
  --, choose --tried replacing it with genDouble
  )
import qualified Data.List as L (nub, groupBy, sort) --TODO should I use strict here? also for all my foldr should I use foldr'? Do I have to do both?
--TODO maybe use Data.List.NonEmpty.groupBy, which provides type-level guarantees of non-emptiness of inner lists.
import SMCDEL.Internal.Help (lfp)
import SNModel
import SetTheory
import Test.QuickCheck.Gen (genDouble)

{-
  Language, simplification of formulas, arbitrary generation of formulas
-}


{-
Adopted agent position means "The agent has adopted the position"
Connected topic agent1 agent2 means "agent1 considers agent2 their friend on the topic."
-}
data Prp = Adopted Agent Position | Connected Topic Agent Agent deriving (Eq,Ord,Show)

{-
modal operators for updates with thresholds
Infl is social influence: Agents change what positions they hold based on their topic-specific
social network. (proportion of friends who hold a position should be larger or equal to tau)
Selec is friendship selection: Agents choose their social connections in each topic-specific social network
based on the proportion of positions they agree on (>= tau)
-}
data UpOperator = Infl Double | Selec Double deriving (Eq, Ord, Show)


{-
Syntax of Social Network Logic (propositional language with
the special atoms Adopted and Connected, and the dynamic operators Infl (Social Influence)
and Selec (Friendship Selection)
-}

--adpapted from symbolic topo-e models
data Form
  = Top
  | Bot
  | PrpF Prp --TODO or should I write the Prp seperately?
  | Neg Form
  | Conj [Form]
  | Disj [Form]
  | Impl Form Form -- faster as primitive (quote Gattinger)
  | Update UpOperator Form --TODO or should I write the updates separately? found out I can pass contstructors...but like this I save writing code for the cases where it just being an update matters. But hen again Gattinger said native implementation is faster
  deriving (Eq, Show, Ord) --Eq needed in simStep :)



--Abbreviations

--TODO are these even needed?

--equivalence <->
equiv :: Form -> Form -> Form
equiv f g = Conj [Impl f g, Impl g f]

--XOR
xor :: Form -> Form -> Form
xor f g = Disj [Conj [f, Neg g], Conj [Neg f, g]]


--translate sequence of updates to formula, no restriction on which type and what tau is used
--Example: updateSeq [up1, up2, up3] f = Update up1 (Update up2 (Update up3 f))
--(simStep will delete consecutive selec operations)
updateSeq :: [UpOperator] -> Form -> Form
updateSeq = flip $ foldr Update


--TODO more abbreviations?

{-
Simplify a formula to an equivalent formula.
Adapted from Symbolic-Topo-E-Models.Syntax.
-}
simplify :: Form -> Form
simplify = lfp simStep    --lfp keeps applying simStep until it doesn't change anything

simStep :: Form -> Form
simStep Top             = Top
simStep Bot             = Bot
simStep (PrpF p)        = PrpF p
simStep (Neg Top)       = Bot
simStep (Neg Bot)       = Top
simStep (Neg (Neg f))   = simStep f
--TODO does this help? bubble the modal operators up? maybe because I can scratch consecutive selec ops
simStep (Neg (Update up f)) = simStep (Update up (Neg f))
simStep (Neg f)         = Neg $ simStep f

--TODO groupByOperator is about same updates with different formulas eg (cross tau m f1 AND cross tau m f2) is equivalent to cross ta (f1 AND f2)
--QUESTION: will the computation of the same updates on the same model even be repeated, so do I
--even need to "bubble up" these operators?

simStep (Conj [])       = Top
simStep (Conj [f])      = simStep f
simStep (Conj fs)      | Bot `elem` fs = Bot
                       | or [ Neg f `elem` fs | f <- fs ] = Bot
                       | otherwise = groupByOperator $ Conj (L.nub $ concatMap unpack fs) where --TODO is it a problem that this is repeated several times?
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
simStep (Disj [])       = Bot
simStep (Disj [f])      = simStep f
simStep (Disj fs)      | Top `elem` fs = Top
                       | or [ Neg f `elem` fs | f <- fs ] = Top
                       | otherwise = groupByOperator $ Disj (L.nub $ concatMap unpack fs) where
                          unpack Bot = []
                          unpack (Disj subfs) = map simStep $ filter (Bot /=) subfs
                          unpack f = [simStep f]
simStep (Impl Bot _)    = Top
simStep (Impl _ Top)    = Top
simStep (Impl Top f)    = simStep f
simStep (Impl f Bot)    = Neg (simStep f)
--bubble up update operator if it's the same on both sides of implication
simStep (Impl f@(Update up1 subF) g@(Update up2 subG)) | up1==up2  = Update up1 (simStep (Impl subF subG))
                                                       | otherwise = Impl (simStep f) (simStep g)
simStep (Impl f g)     | f==g      = Top
                       | otherwise = Impl (simStep f) (simStep g)
simStep (Update _ Bot)  = Bot
simStep (Update _ Top)  = Top

--Friendship selection: if applied twice in a row (no matter the tau), the first applied is irrelevant
--ACHTUNG TODO this only applies to the basic version, for variations think about it again!
simStep (Update (Selec _) (Update (Selec tau) f)) = simStep (Update (Selec tau) f)

--After selec 1, influence won't change anything
--ACHTUNG TODO das ist nur korrekt ohne die Variations
simStep (Update (Selec 1) (Update (Infl _) f)) = Update (Selec 1) (simStep f)

{-
Update Selec does not impact positions.
Therefore if we only check a boolean combination of Adopted propositions,
  we can skip computing the update.
Also, we eliminate the outer application of selec, if it's applied to a list of formulas, that
  start with a selec anyway
-}
simStep (Update s@(Selec tau) f) | boolOfAdopted f = simStep f --(in later recursions inner selecs get eliminated anyway if applicable)
                                 | isListOfSelec f = simStep f
                                 | tau==1 && isListOfInfl f = simStep (removeFirstOp f) -- too specific? also only correct in basic version, not for variations
                                 | otherwise = Update s (simStep f)

{-
Update Infl does not impact connections.
Therefore if we only check a boolean combination of Connected propositions,
  we can skip computing the update.
-}
simStep (Update i@(Infl _) f)  | boolOfConnected f = simStep f
                               | otherwise = Update i (simStep f)


--simStep (Update up f)   = Update up (simStep f) --currently replaced in the two previous matches



--Checks if a given formula is a boolean combination of Adopted Propositions.
boolOfAdopted :: Form -> Bool
boolOfAdopted Top                   = True
boolOfAdopted Bot                   = True
boolOfAdopted (PrpF (Adopted _ _))  = True
boolOfAdopted (PrpF (Connected {})) = False
boolOfAdopted (Neg f)               = boolOfAdopted f
boolOfAdopted (Conj xs)             = all boolOfAdopted xs
boolOfAdopted (Disj xs)             = all boolOfAdopted xs
boolOfAdopted (Impl f g)            = boolOfAdopted f && boolOfAdopted g
boolOfAdopted (Update _ _)          = False


--Checks if a given formula is a boolean combination of Connected Propositions.
boolOfConnected :: Form -> Bool
boolOfConnected Top                   = True
boolOfConnected Bot                   = True
boolOfConnected (PrpF (Connected {})) = True
boolOfConnected (PrpF (Adopted _ _))  = False
boolOfConnected (Neg f)               = boolOfConnected f
boolOfConnected (Conj xs)             = all boolOfConnected xs
boolOfConnected (Disj xs)             = all boolOfConnected xs
boolOfConnected (Impl f g)            = boolOfConnected f && boolOfConnected g
boolOfConnected (Update _ _)          = False


--checks is a formula is a conjunction or disjunction of formulas that start with an application of Selec
isListOfSelec :: Form -> Bool
isListOfSelec (Conj xs) = all isSelec xs --returns true for empty list
isListOfSelec (Disj xs) = all isSelec xs
isListOfSelec _         = False

--checks if a given formula starts with an application of Selec
isSelec ::  Form -> Bool
isSelec (Update (Selec _) _) = True
isSelec _                    = False

--checks is a formula is a conjunction or disjunction of formulas that start with an application of Infl
isListOfInfl :: Form -> Bool
isListOfInfl (Conj xs) = all isInfl xs
isListOfInfl (Disj xs) = all isInfl xs
isListOfInfl _         = False

--checks if a given formula starts with an application of Infl
isInfl :: Form -> Bool
isInfl (Update (Infl _) _) = True
isInfl _                   = False



--will only be called for length xs > 1
groupByOperator :: Form -> Form
groupByOperator (Conj xs) = Conj (concatMap (bubbleUpOp Conj) (L.groupBy hasSameOp (L.sort xs))) --if this is a singleton list, it will be simplified in the next round
groupByOperator (Disj xs) = Disj (concatMap (bubbleUpOp Disj) (L.groupBy hasSameOp (L.sort xs)))
groupByOperator f         = f --only here for pattern exhaustion



hasSameOp :: Form -> Form -> Bool
hasSameOp (Update up1 _) (Update up2 _) = up1==up2
hasSameOp (Update _ _) _                = False
hasSameOp _ (Update _ _)                = False
hasSameOp _ _                           = True --TODO check if this correct, want to have one group of all the ones that don't start with an update

{-
The first argument is a constructur of Form (Conj or Disj).
The second argument a (per groupBy non-empty) list  of forms that start with the same update operator.
  or: they all don't start with an update Operator at all.
It will bubble up that shared Update operator.
Example: TODO
-}
bubbleUpOp :: ([Form] -> Form) -> [Form] -> [Form]
bubbleUpOp _ [x]           = [x] --do nothing, if is a singleton list
bubbleUpOp constr ((Update up1 x):xs) = [Update up1 (removeFirstOp (constr (x:xs)))]
bubbleUpOp _ xs                       = xs    --list of stuff that doesn't start with an Update Operator

--intended only to be used for Forms that are lists of forms that start with update operator
removeFirstOp :: Form -> Form
removeFirstOp (Update _ f) = f
removeFirstOp (Conj xs)    = Conj (map removeFirstOp xs)
removeFirstOp (Disj xs)    = Disj (map removeFirstOp xs)
removeFirstOp g            = g --only here for pattern exhaustion, should never be used

{-
generate an Arbitrary Proposition

alternatively we could use a defined defaultVocab. something like:

defaultVocab :: Set Agent -> M.Map Topic (Set Position) -> [Prp]
defaultVocab agents' positions' = adopteds ++ connecteds where
  adopteds = [Adopted ag p | ag <- S.toList agents', p <- S.toList $ allPos positions']
  connecteds = [Connected t a1 a2 | a1 <- S.toList agents', a2 <- S.toList agents', t <- M.keys positions']
-}
instance Arbitrary Prp where
  arbitrary = oneof [ Adopted <$> intSetElements defaultAgents <*> (arbitrary::Gen Position) --TODO list conversion
                    , Connected <$> (arbitrary::Gen Topic) <*> intSetElements defaultAgents <*> intSetElements defaultAgents
                    ]


{-
generate Arbitrary Update Operator
-}

--TODO check if this works!
instance Arbitrary UpOperator where
  arbitrary = oneof [ Infl <$> genDouble
                    , Selec <$> genDouble]

{-
  Generate arbitrary sized formulas.
  Adapted from Symbolic-Topo-E-Models.Syntax.
-}
instance Arbitrary Form where
    arbitrary = sized randomForm
      where
        randomForm :: Int -> Gen Form
        randomForm 0 = oneof [ --pure Top
                             --, pure Bot, --TODO commented out for testing
                              PrpF <$> (arbitrary::Gen Prp)
                             ]
        randomForm n = oneof [ --pure Top
                             --, pure Bot, --TODO commented out for testing
                              PrpF <$> (arbitrary::Gen Prp)
                             , Neg <$> st
                             , Conj <$> listOf st
                             , Disj <$> listOf st
                             , Impl <$> st <*> st
                             , Update <$> (arbitrary::Gen UpOperator) <*> st
                             ]
          where
            st = randomForm (n `div` 3)

--TODO is this the only way to get it to generate later in ghci?
getGenForm :: Gen Form
getGenForm = arbitrary :: Gen Form

{-
usage in ghci:
import Test.QuickCheck (generate)
myForm <- generate getGen --(default sized passed is 30)
simplify myForm
generate $ resize 20 getGen
-}


--TODO needed? copied from Symbolic-Topo-E-Models.Syntax

-- Boolean formulas (adapted from SMCDEL.Language to work with our Form type).

{-}
newtype BF = BF Form deriving (Eq,Ord,Show)

-- Generate arbitrary sized boolean formulas.
randomBFWith :: [Prp] -> Int -> Gen BF
randomBFWith allprops sz = BF <$> bf' sz where
  bf' 0 = PrpF <$> elements allprops
  bf' n = oneof [ pure Top
                , pure Bot
                , PrpF <$> elements allprops
                , Neg <$> st
                , (\x y -> Conj [x,y]) <$> st <*> st
                , (\x y z -> Conj [x,y,z]) <$> st <*> st <*> st
                , (\x y -> Disj [x,y]) <$> st <*> st
                , (\x y z -> Disj [x,y,z]) <$> st <*> st <*> st
                , Impl <$> st <*> st
                ]
    where
      st = bf' (n `div` 3)

instance Arbitrary BF where
  arbitrary = sized $ randomBFWith defaultVocab

-}


