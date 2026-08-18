{-# LANGUAGE TupleSections #-}

module SNModel where

import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf  )
import Test.QuickCheck.Gen (chooseInt)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S -- Set is strict ;)

import Data.Set (Set)
import qualified Data.IntSet as IntSet
import SetTheory
import Data.Bits (testBit)
import qualified Data.Vector as V

{-
Explicit representation of Social Network Models following Smets et al. (2020)
Relational Kripke models, per Def with
 - a non-empty, finite set of agents as the domain
 - a non-empty, finite set of topics
 - for each topic a non-empty, finite set of positions on the topic. These sets are pairwise disjoint.
 - a binary relation for each topic (= social network).)
-}

{-
Social networks don't have to satisfy any properties
(i.e. they can be reflexive and non-symmetric).
-}


{-
Assumptions on the form of SNM: (that aren't enforced here, but should be checked before working with a model)

(1) All sets/maps should by def be non-empty.
(2) The sets of Positions are pairwise disjoint across topics. TODO manually double them when a provided model violates this.
(3) The maps contain every topic of the model as a key. Dual_t only contains agents as keys who have non-empty set of positions in that topic
-}

--no friends is very rare -> vector
--no position is NOT rare -> Map

data SNModel = SNM
 { nrAgents :: Int --agents are referred to by 0 .. (nrAgents - 1)
 , positions :: M.Map Topic (Set Position) --pairwise disjoint sets ACHTUNG TODO : TOPICS CAN NOT INCLUDE (T 0), that's a special case reserved for internal use!
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key
 , dual :: M.Map Topic (IntMap (Set Position)) --every topic should be a key, but only agents taking more than 0 positions are keys (bc no position taken is also quite common)
 } deriving (Eq, Show)
--TODO maybe write a better Show?




--See definitions for Agent/Relation in SetTheory.hs

newtype Topic = T Int deriving (Eq, Show, Ord) --T 0 is reserved for internal use
newtype Position = P Int deriving (Eq, Show, Ord)


--CHANGE default values if neded
defaultNrAgs, nrTpcs, nrPosTotal :: Int
defaultNrAgs = 120
nrTpcs = 2
nrPosTotal = 6 --number of positions in total, make sure nrPosTotal >= nrTpcs


{-
Input: SNModel
Output: Valuation corresponding to the dual
-}
val :: SNModel -> M.Map Topic (M.Map Position IntSet.IntSet)
val snm = M.fromList [(t, val_t snm t)| t <- topics] where
  topics = M.keys $ positions snm

{-
Input: SNModel, Topic
Output: Valuation for the given Topic
-}

--TODO test
--TODO I think positions that aren't taken by anyone won't be in the map at all
val_t :: SNModel -> Topic -> M.Map Position IntSet.IntSet
val_t snm t =  M.fromListWith IntSet.union
    [ (p, IntSet.singleton i)
    | (i, ps) <- dual_t_list
    , p <- S.toList ps
    ] where
  dual_t = dual snm M.! t
  dual_t_list =  IntMap.toList dual_t


--TODO test
{-
Input: Valuation for a specific topic.
Output: Corresponding dual for that topic.
Agents that don't hold any position of that topic don't appear in the map.
-}
valToDual_t :: M.Map Position IntSet.IntSet -> IntMap (Set Position)
valToDual_t val_t' = IntMap.fromListWith S.union
    [ (i, S.singleton p)
    | (p, is) <- val_t_list
    , i <- IntSet.toList is
    ] where
  val_t_list = M.toList val_t'

{-
some hardcoded examples
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

a, b, c, d, ab, ac, bc, abc, ad, cd, acd :: AgentSet
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

{-
TODO construct better example!
this one hardly changes for the Infl operation
-}
exampleSmall :: SNModel
exampleSmall = SNM 3 positions' rel' dual' where
    positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
    rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = V.fromList [abc, IntSet.empty, ac]
        gamesRel = V.fromList [IntSet.empty, b, b]
        sportsRel = V.fromList [ac, IntSet.empty, a]
    dual' = M.fromList [(books, bookdual) , (games, gamesdual), (sports, sportsdual)] where
        bookdual = IntMap.fromList [(0, S.fromList [fantasy, romance]), (1, S.singleton romance), (2, S.fromList [fantasy, nonFiction])]
        gamesdual = IntMap.fromList [(1, S.singleton cardGames), (2, S.fromList [boardGames, cardGames])]
        sportsdual = IntMap.fromList [(0, S.fromList [teamSports,endurance,weights]), (1, S.singleton weights), (2, S.fromList [weights, endurance])]


{-
--TODO bit of a boring example, it's for simple testing of the settheory stuff
exampleCircleFriendship :: SNModel
exampleCircleFriendship = SNM 4 positions' rel' val' where
  --group = IntSet.fromList [alice, bob, carol, david]
  positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
  rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = M.fromList [(alice, b),(bob, c),(carol, d), (david,a)]
        gamesRel = M.fromList [(alice, b),(bob, c),(carol, d), (david,a)]
        sportsRel = M.fromList [(alice, b),(bob, c),(carol, d), (david,a)]
  val' = M.fromList [(fantasy, ac), (romance, ab), (nonFiction, c), (cardGames, bc), (boardGames, c), (rolePlaying, IntSet.empty), (teamSports, a), (endurance, ac), (weights, abc)]
-}


--example to test stabilization

exampleStab :: Int -> SNModel
exampleStab n = SNM stabAgSize positions' rel' dual'  where
  stabPosSize = n
  stabAgSize = 2^n
  positions' = M.singleton (T 1) (S.fromList $ map P [1..stabPosSize])
  rel'       = M.singleton (T 1) $ makeEmptyRel stabAgSize
  dual'      = M.singleton (T 1) (foldl (\cur i -> IntMap.insert i (constructSet i) cur) IntMap.empty [0..stabAgSize-1]) where
    constructSet i = S.fromList $ map (P . (+1)) $ filter (testBit i) [0..(stabPosSize-1)]



exampleStab2 :: SNModel
exampleStab2 = SNM 4 positions' rel' dual' where
  positions' = M.singleton (T 1) (S.fromList [P 1, P 2, P 3, P 4, P 5, P 6])
  rel'       = M.singleton (T 1) $ makeEmptyRel 4
  dual'      = M.singleton (T 1) (IntMap.fromList [(0, S.empty), (1, S.fromList [P 3, P 4, P 5, P 6]), (2, S.fromList [P 1, P 5, P 6]), (3, S.fromList [P 1, P 3, P 4])])
-- ACHTUNG ! ..
--TODO make it safe (like break at 100 or something)
{-
Runs a function f until stabilization (output == input) and
returns stabilized output and the number of iterations it took to get there.
-}
fixCount :: Eq a => (a -> a) -> a -> (a, Int)
fixCount f = go 0
  where
    go k current =
      let x' = f current
      in if x' == current
           then (current, k)
           else go (k + 1) x'


--TODO replace occurance of fixCount with this?
stabCountSafe :: Eq a => Int -> (a -> a) -> a -> (a, Maybe Int)
stabCountSafe maxIter f = go 0
  where
    go k current
      | k >= maxIter = (current, Nothing)
      | x' == current = (current, Just k)
      | otherwise = go (k + 1) x'
      where
        x' = f current



examplePaper :: SNModel
examplePaper = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..4]), (T 2, S.fromList $ map P [5..8]), (T 3, S.fromList $ map P [9..12])]
  rel' = M.fromList $ zip (map T [1,2,3]) $ replicate 3 (makeEmptyRel 4)
  dual' = M.fromList [(T 1, fDual), (T 2, mDual), (T 3, sDual)]
  fDual = IntMap.fromList [(0, S.fromList [P 2, P 3, P 4]), (1, S.singleton (P 2)), (2, S.fromList [P 1, P 3, P 4]), (3, S.fromList [P 3,P 4])]
  mDual = IntMap.fromList [(0, S.singleton (P 5)), (1,S.fromList [P 6, P 7]), (2, S.singleton (P 8)), (3, S.fromList [P 5, P 6, P 7])]
  sDual = IntMap.fromList [(0, S.fromList [P 9, P 10, P 11, P 12]), (1, S.singleton (P 11)), (2, S.fromList [P 9, P 12]), (3, S.fromList [P 9, P 10])]

exampleLogicSection :: SNModel
exampleLogicSection = SNM 4 positions' rel' dual' where
  positions' = M.fromList [(T 1, S.fromList $ map P [1..3]), (T 2, S.fromList $ map P [4..6])]
  rel' = M.fromList [(T 1, V.fromList [a, a, ad, a]), (T 2, V.fromList [a, b, c, d])]
  dual' = M.fromList [(T 1, bDual), (T 2, sDual)]
  bDual = IntMap.fromList [(0, S.fromList [P 1, P 2]), (1, S.singleton (P 2)), (2, S.fromList [P 2, P 3]), (3, S.fromList [P 2,P 3])]
  sDual = IntMap.fromList [(0, S.singleton (P 4)), (1,S.fromList [P 4, P 5, P 6]), (2, S.fromList [P 5, P 6]), (3, S.singleton (P 5))]



{-
these work with the provided lists of agents/topics/positions, not only with the default :)
so it can also be used for generating a model based on user input...
It uses lists instead of sets, bc the sublist function would require list conversion anyway
-}


{-
Given a list a number agents, generates an arbitrary binary relation.
-}

{- ussage in ghci:
import Test.QuickCheck
generate (randomRel 4)
-}
randomRel :: Int -> Gen Relation
randomRel nrAgs = do
  list <- randomRelList nrAgs nrAgs
  return $ V.fromList list

--second argument it the recursively decreasing one
randomRelList :: Int -> Int -> Gen [IntSet.IntSet]
randomRelList _ 0 = return []
randomRelList nrAgs n = do
    thisAgsFriends <- IntSet.fromList <$> sublistOf [0..nrAgs-1]  -- TODO two ideas for less dense (averarage degree is now n/2) -> either pick from sublist again (should halve the probability) or restrict to numerical value (like in case study, recursively pick until you reach a number between x and y)try restrictin (but not like this, it couldn't generate)`suchThat` (\xs -> length xs <= (nrAgs `div` 10))
    rest <- randomRelList nrAgs (n-1)
    return $ thisAgsFriends:rest


{-
  Given a list of agents and a list of topics (both duplicate-free), generates an arbitrary
  relation for each topic. This function applies randomRel to each topic.
  adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}
randomRelMap :: Int -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap nrAgs (t:tpcs) =  do
    thisTpcsRel <- randomRel nrAgs
    rest <- randomRelMap nrAgs tpcs
    return $ M.insert t thisTpcsRel rest


{-
Given a list of positions of a certain topic and a list of agents (both duplicate free), generate a random dual (Map from Agent to Subset of those Positions)
-}
randomDualT :: Set Position -> [Agent] -> Gen (IntMap (Set Position))
randomDualT _ [] = return IntMap.empty
randomDualT pos (ag:ags) = do
    thisAgsPos <- subsetOf pos
    rest <- randomDualT pos ags
    if S.size thisAgsPos > 0 then
      return $ IntMap.insert ag thisAgsPos rest
    else
      return rest

--takes the positions map and a list of agents, applies randomDualT for each topic
--then returns randomDual
randomDualMap :: M.Map Topic (Set Position) -> [Agent] -> Gen (M.Map Topic (IntMap (Set Position)))
randomDualMap posMap ags = traverse (`randomDualT` ags) posMap


--assumes length list >= Int
--takes an Int and a list. generates a partition with exactly Int number of non-empty subsets
randomPart :: Int -> [a] -> Gen [[a]]
randomPart 1 xs = return [xs]
randomPart l xs = do
  let n = length xs
  thisLength <- chooseInt (1, n - l + 1) --make sure the rest of the (l-1) partitions still get at least one element each
  let (first, rest) = splitAt thisLength xs
  restPart <- randomPart (l-1) rest
  return $ first : restPart


{-
given a list of topics and a list of positions (both duplicate free & non-empty, ASSUMES length ps>=length ts)
generate a mapping from topics to sets of positions (pairwise disjoint, non-empty)
-}
randomPosMap :: [Topic] -> [Position] -> Gen (M.Map Topic (Set Position))
randomPosMap ts ps = do
  partition <- randomPart (length ts) ps
  return $ M.fromList $ zipWith (\t partP -> (t, S.fromList partP)) ts partition


{-
  Generate an arbitrary Social Network model.
    adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}
instance Arbitrary SNModel where
  arbitrary = do
    --TODO limit some stuff? (not necessary, bc I don't close under reflexivity/transitivity?)
    let tpcs = map T [1..nrTpcs] --fixed for formula generation purposes
        pos = map P [1..nrPosTotal] --fixed for formula generation purposes
    randomTPMap <- randomPosMap tpcs pos
    randomRels <- randomRelMap defaultNrAgs tpcs
    randomDual <- randomDualMap randomTPMap [0..defaultNrAgs-1]
    return (SNM defaultNrAgs randomTPMap randomRels randomDual)




--takes a SNModel and makes full relations for all topics
makeFullRelModel :: SNModel -> SNModel
makeFullRelModel m@(SNM nrAgents' pos' _ _) = m { rel = fullRels } where
    fullRels = M.fromList $ map (, fullRel) (M.keys pos')
    fullRel = makeFullRel nrAgents'


makeFullRel :: Int -> Relation
makeFullRel n = V.replicate n $ IntSet.fromList [0..(n-1)]

--takes a number of agents and creates an empty Relation
makeEmptyRel :: Int -> Relation
makeEmptyRel n = V.replicate n IntSet.empty


--takes a SNModel and makes all its relations reflexive
makeReflModel :: SNModel -> SNModel
makeReflModel m@(SNM _ _ rel' _) = m {rel = M.map makeReflexive rel'}

--takes a SNmodel and makes all its relations symmetric
makeSymModel :: SNModel -> SNModel
makeSymModel m@(SNM _ _ rel' _) = m {rel = M.map makeSymmetric rel'}

--takes a SNModel and makes all its relations transitive
makeTransModel :: SNModel -> SNModel
makeTransModel m@(SNM _ _ rel' _) = m {rel = M.map makeTransitive rel'}


{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel
-}


