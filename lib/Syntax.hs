module Syntax where


--TODO do only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sized
  --, elements --might need this later
  , oneof
  , listOf
  --, choose -- needed for dynamics later
  )
import Data.List (nub)
import SMCDEL.Internal.Help (lfp)
import SNModel
import qualified SMCDEL.Explicit.DEMO_S5 as Proposition


{-
  Language, simplification of formulas, arbitrary generation of formulas
-}


{-
Adopted agent position means "The agent has adopted the position"
Connected topic agent1 agent2 means "agent1 considers agent2 their friend on the topic."
-}
data Prp = Adopted Agent Position | Connected Topic Agent Agent deriving (Eq,Ord,Show)

{-
Syntax of Social Network Logic (propositional language with
the special atoms Adopted and Connected, and the dynamic operators Infl (Social Influence)
and Selec (Friendship Selection)
-}

--adpapted from symbolic topo-e models
data Form
  = Top
  | Bot
  | PrpF Prp
  | Neg Form
  | Conj [Form]
  | Disj [Form]
  | Impl Form Form
  -- | Infl Double Form -- TODO add dynamics
  -- | Selec Double Form
  deriving (Eq, Show, Ord) --Eq needed in simStep :)


--Abbreviations

--equivalence <->
equiv :: Form -> Form -> Form
equiv f g = Conj [Impl f g, Impl g f]

xor :: Form -> Form -> Form
xor f g = Disj [Conj [f, Neg g], Conj [Neg f, g]]


--TODO more abbreviations involcing dynamics, e.g. sequence of updates


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
--TODO include dynamics
--simStep (Infl _ Bot)    = Bot
--simStep (Infl _ Top)    = Top
--simStep (Infl tau f)    = Infl tau (simStep f)
--simStep (Selec _ Bot)   = Bot
--simStep (Selec _ Top)   = Top
--simStep (Selec tau f)   = Selec tau (simStep f)



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
                             --, Infl <$> choose (0,1) <*> st -- TODO is this a save way to get a random tau?
                             --, Selec <$> choose (0,1) <*> st
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


