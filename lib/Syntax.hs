module Syntax where


--TODO do only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sized

  , oneof
  , listOf
  , choose
  )
import Data.List (nub)
import SMCDEL.Internal.Help (lfp)
import SNModel

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
  | Impl Form Form --TODO or should I do this using an abbreviation?
  | Update UpOperator Form --TODO or should I write the updates separately? did this so I could have a sequence of them
  deriving (Eq, Show, Ord) --Eq needed in simStep :)



--Abbreviations

--TODO are these even needed?

--equivalence <->
equiv :: Form -> Form -> Form
equiv f g = Conj [Impl f g, Impl g f]

--XOR
xor :: Form -> Form -> Form
xor f g = Disj [Conj [f, Neg g], Conj [Neg f, g]]


--sequence of updates, no restriction on which type and what tau is used
--simStep will delete consecutive selec operations
updateSeq :: [UpOperator] -> Form -> Form
updateSeq = flip $ foldr Update


--TODO more abbreviations?

{-
Simplify a formula to an equivalent formula.
Adapted from Symbolic-Topo-E-Models.Syntax.
-}
simplify :: Form -> Form
simplify = lfp simStep

simStep :: Form -> Form
simStep Top             = Top
simStep Bot             = Bot
simStep (PrpF p)        = PrpF p
simStep (Neg Top)       = Bot
simStep (Neg Bot)       = Top
simStep (Neg (Neg f))   = simStep f
simStep (Neg f)         = Neg $ simStep f
simStep (Conj [])       = Top
simStep (Conj [f])      = simStep f
simStep (Conj fs)      | Bot `elem` fs = Bot
                       | or [ Neg f `elem` fs | f <- fs ] = Bot
                       | otherwise = Conj (nub $ concatMap unpack fs) where
                          unpack Top = []
                          unpack (Conj subfs) = map simStep $ filter (Top /=) subfs
                          unpack f = [simStep f]
simStep (Disj [])       = Bot
simStep (Disj [f])      = simStep f
simStep (Disj fs)      | Top `elem` fs = Top
                       | or [ Neg f `elem` fs | f <- fs ] = Top
                       | otherwise = Disj (nub $ concatMap unpack fs) where
                          unpack Bot = []
                          unpack (Disj subfs) = map simStep $ filter (Bot /=) subfs
                          unpack f = [simStep f]
simStep (Impl Bot _)    = Top
simStep (Impl _ Top)    = Top
simStep (Impl Top f)    = simStep f
simStep (Impl f Bot)    = Neg (simStep f)
simStep (Impl f g)     | f==g      = Top
                       | otherwise = Impl (simStep f) (simStep g)

--dynamics
simStep (Update _ Bot)  = Bot
simStep (Update _ Top)  = Top
--Friendship selection: if applied twice in a row with different tau, the first applied is irrelevant
--ACHTUNG TODO this only applies to the basic version, for variations think about it more!
simStep (Update (Selec tau) (Update (Selec _) f)) = simStep (Update (Selec tau) f)
--After selec 1, influence won't change anything
--ACHTUNG TODO das ist nur korrekt ohne die Variations
simStep (Update (Infl _) (Update (Selec 1) f)) = Update (Selec 1) (simStep f)
simStep (Update up f)   = Update up (simStep f)





{-
generate an Arbitrary Proposition

alternatively we could use a defined defaultVocab. something like:

defaultVocab :: Set Agent -> M.Map Topic (Set Position) -> [Prp]
defaultVocab agents' positions' = adopteds ++ connecteds where
  adopteds = [Adopted ag p | ag <- S.toList agents', p <- S.toList $ allPos positions']
  connecteds = [Connected t a1 a2 | a1 <- S.toList agents', a2 <- S.toList agents', t <- M.keys positions']
-}
instance Arbitrary Prp where
  arbitrary = oneof [ Adopted <$> (arbitrary::Gen Agent) <*> (arbitrary::Gen Position)
                    , Connected <$> (arbitrary::Gen Topic) <*> (arbitrary::Gen Agent) <*> (arbitrary::Gen Agent)
                    ]


{-
generate Arbitrary Update Operator
-}

instance Arbitrary UpOperator where
  arbitrary = oneof [ Infl <$> choose (0,1)
                    , Selec <$> choose (0,1)]

{-
  Generate arbitrary sized formulas.
  Adapted from Symbolic-Topo-E-Models.Syntax.
-}
instance Arbitrary Form where
    arbitrary = sized randomForm
      where
        randomForm :: Int -> Gen Form
        randomForm 0 = oneof [ pure Top
                             , pure Bot
                             , PrpF <$> (arbitrary::Gen Prp)
                             ]
        randomForm n = oneof [ pure Top
                             , pure Bot
                             , PrpF <$> (arbitrary::Gen Prp)
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


