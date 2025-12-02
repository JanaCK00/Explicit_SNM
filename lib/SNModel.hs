module SNModel where

--TODO only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf  )
import Test.QuickCheck.Gen (chooseInt)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S -- Set is strict ;)
--import Data.Map.Strict ((!))
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import SetTheory
import Data.Bits (testBit)

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
(2) The sets of Positions are pairwise disjoint across topics. TODO manually double them when a provded model violates this.
(3) All Maps are full (every Topic or Positions respectively is a key (even if it just maps to the empty set))
-}

--TODO change that the maps aren't full???? so you save space when many people e.g. don't have friends, you also get faster lookips for sparse case
--and: for the dual, you could also save the agents that don't have a positions on that topic...
--PROBLEM: in my semantics, I'd have to go about it quite differently (safe lookups, can't just mapwithkey over the old map, bc some agents might be inserted or deleted from a map)
data SNModel = SNM
 { nrAgents :: Int --agents are referred to by 1..nrAgents
 , positions :: M.Map Topic (Set Position) --pairwise disjoint sets. this could actually also be a map of sizes and then have the topic in the position like i planned originally...and you only need the list of positions for a topic to go through for the annpying case of Infl 0...BUT: for UpdInfl it's cleaner to have stuff seperated by topics, we couldn't merge the dual maps. And then you hae to carry the info around, for each operation
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key
 , dual :: M.Map Topic (IntMap (Set Position)) --every topic should be a key, every agent in each submap should be a key TODO maybe not every agent should be a key...it's not too unlikely that they don't take any position on a certain topic
 } deriving (Eq, Show)


--See definitions for Agent/Relation in SetTheory.hs

newtype Topic = T Int deriving (Eq, Show, Ord)
newtype Position = P Int deriving (Eq, Show, Ord)


--CHANGE default values if neded
defaultNrAgs, nrTpcs, nrPosTotal :: Int
defaultNrAgs = 100
nrTpcs = 10
nrPosTotal = 100 --number of positions in total, make sure nrPosTotal >= (2*)nrTpcs



{-
some hardcoded examples
-}


alice, bob, carol, danny, emily :: Int
alice = 1
bob = 2
carol = 3
danny = 4
emily = 5

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

teamSports, running, weights :: Position
teamSports = P 7
running = P 8
weights = P 9

sportsPositions :: Set Position
sportsPositions = S.fromList [teamSports, running, weights]

a, b, c, d, ab, ac, bc, abc :: AgentSet
a = IntSet.singleton alice
b = IntSet.singleton bob
c = IntSet.singleton carol
ab = IntSet.fromList [alice, bob]
ac = IntSet.fromList [alice, carol]
bc = IntSet.fromList [bob, carol]
abc = IntSet.fromList [alice, bob, carol]
d = IntSet.singleton danny

{-
TODO construct better example!
this one hardly changes for the Infl operation
-}
exampleSmall :: SNModel
exampleSmall = SNM 3 positions' rel' dual' where
    positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
    rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = IntMap.fromList [(alice, abc),(bob, IntSet.empty),(carol, ac)]
        gamesRel = IntMap.fromList [(alice, IntSet.empty), (bob, b),(carol, b)]
        sportsRel = IntMap.fromList [(alice, ac), (bob, IntSet.empty), (carol, a)]
    dual' = M.fromList [(books, bookdual) , (games, gamesdual), (sports, sportsdual)] where
        bookdual = IntMap.fromList [(1, S.fromList [fantasy, romance]), (2, S.singleton romance), (3, S.fromList [fantasy, nonFiction])]
        gamesdual = IntMap.fromList [(1, S.empty), (2, S.singleton cardGames), (3, S.fromList [boardGames, cardGames])]
        sportsdual = IntMap.fromList [(1, S.fromList [teamSports,running,weights]), (2, S.singleton weights), (3, S.fromList [weights, running])]


{-
--TODO bit of a boring example, it's for simple testing of the settheory stuff
exampleCircleFriendship :: SNModel
exampleCircleFriendship = SNM 4 positions' rel' val' where
  --group = IntSet.fromList [alice, bob, carol, danny]
  positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
  rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = M.fromList [(alice, b),(bob, c),(carol, d), (danny,a)]
        gamesRel = M.fromList [(alice, b),(bob, c),(carol, d), (danny,a)]
        sportsRel = M.fromList [(alice, b),(bob, c),(carol, d), (danny,a)]
  val' = M.fromList [(fantasy, ac), (romance, ab), (nonFiction, c), (cardGames, bc), (boardGames, c), (rolePlaying, IntSet.empty), (teamSports, a), (running, ac), (weights, abc)]
-}


--example to test stabilization

exampleStab :: Int -> SNModel
exampleStab n = SNM stabAgSize positions' rel' dual'  where
  stabPosSize = n
  stabAgSize = 2^n
  positions' = M.singleton (T 1) (S.fromList $ map P [1..stabPosSize])
  rel'       = M.singleton (T 1) $ makeEmptyRel stabAgSize
  dual'      = M.singleton (T 1) (foldl (\cur i -> IntMap.insert i (constructBitSet i) cur) IntMap.empty [1..stabAgSize]) where
    constructBitSet i = S.fromList $ map (P . (+1)) $ filter (testBit i) [0..(stabPosSize-1)]


-- ACHTUNG ! .. !
fixCount :: Eq a => (a -> a) -> a -> (a, Int)
fixCount f = go 0
  where
    go k x =
      let x' = f x
      in if x' == x
           then (x, k)
           else go (k + 1) x'

examplePaper :: SNModel
examplePaper = SNM 4 positions' rel' dual' where
  positions' = M.singleton (T 1) (S.fromList $ map P [1..4])
  rel' = M.singleton (T 1) $ makeEmptyRel 4
  dual' = M.singleton (T 1) (IntMap.fromList [(1, S.singleton (P 1)), (2,S.fromList [P 2, P 3]), (3, S.singleton (P 4)), (4, S.fromList [P 1, P 2, P 3])])



{-
these work with the provided lists of agents/topics/positions, not only with the default :)
so it can also be used for generating a model based on user input...
It uses lists instead of sets, bc the sublist function would require list conversion anyway
-}

{-
Given a list of agents (duplicate-free), (second argument is the recursively decreasing one),
generates an arbitrary binary relation.
-}
randomRel :: [Agent] -> [Agent] -> Gen Relation
randomRel _ [] = return IntMap.empty
randomRel allAgs (ag:ags) = do
    thisAgsFriends <- IntSet.fromList <$> sublistOf allAgs --TODO if this is empty -> don't add to map?
    rest <- randomRel allAgs ags
    return $ IntMap.insert ag thisAgsFriends rest

{-
  Given a list of agents and a list of topics (both duplicate-free), generates an arbitrary
  relation for each topic. This function applies randomRel to each topic.
  adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}
randomRelMap :: [Agent] -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap ags (t:tpcs) =  do
    thisTpcsRel <- randomRel ags ags
    rest <- randomRelMap ags tpcs
    return $ M.insert t thisTpcsRel rest


{-
TODO maybe delete, not used
{-
Given a list of agents and a list of positions (both duplicate-free), generate a random Valuation
-}
randomVal :: [Agent] -> [Position] -> Gen (M.Map Position AgentSet)
randomVal _ [] = return M.empty
randomVal ags (p:pos) = do
    thisPosAgs <- IntSet.fromList <$> sublistOf ags
    rest <- randomVal ags pos
    return $ M.insert p thisPosAgs rest
-}


{-
Given a list of positions of a certain topic and a list of agents (both duplicate free), generate a random dual (Map from Agent to Subset of those Positions)
-}
randomDualT :: Set Position -> [Agent] -> Gen (IntMap (Set Position))
randomDualT _ [] = return IntMap.empty
randomDualT pos (ag:ags) = do
    thisAgsPos <- subsetOf pos --TODO if this is empty -> don't add to map?
    rest <- randomDualT pos ags
    return $ IntMap.insert ag thisAgsPos rest


--takes the positions map and a list of agents, applies randomDualT for each topic
--then returns randomDual
randomDualMap :: M.Map Topic (Set Position) -> [Agent] -> Gen (M.Map Topic (IntMap (Set Position)))
randomDualMap posMap ags = traverse (`randomDualT` ags) posMap


--TODO decide if topics with just one positions even make sense...right now it gives at least 2 positions per topic
--assumes length list >= Int
--takes an Int and a list. generates a partition with exactly Int number of  non-empty subsets
randomPart :: Int -> [a] -> Gen [[a]]
randomPart 1 xs = return [xs]
randomPart l xs = do
  let n = length xs
  thisLength <- chooseInt (2, n - 2*(l - 1)) --make sure the rest of the (l-1) partitions still get at least two elements each
  let (first, rest) = splitAt thisLength xs
  restPart <- randomPart (l-1) rest
  return $ first : restPart


{-
given a list of topics and a list of positions (both duplicate free & non-empty, ASSUMES length ps>=length ts)
generate a mapping from topics to sets of positions (pariwise disjoint, non-empty)
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
    let ags = [1..defaultNrAgs] --TODO could change this to have different number of agents, be the nr between 1 and defaultNrAgs
        tpcs = map T [1..nrTpcs] --here too
        pos = map P [1..nrPosTotal] --and then this could be between number of tpcs and like 10-20 times that
    randomTPMap <- randomPosMap tpcs pos
    randomRels <- randomRelMap ags tpcs
    randomDual <- randomDualMap randomTPMap ags
    return (SNM defaultNrAgs randomTPMap randomRels randomDual)




--takes a SNModel and makes full relations for all topics
makeFullRelModel :: SNModel -> SNModel
makeFullRelModel m@(SNM nrAgents' _ rel' _) = m { rel = M.map fullRel rel' } where
    fullRel = IntMap.map allFriends
    allFriends _ = IntSet.fromList [1..nrAgents']


--TODO check if this works
--takes a number of agents and creates an empty Relation (each agent is a key in the map)
makeEmptyRel :: Int -> Relation
makeEmptyRel n = foldl (\cur i -> IntMap.insert i IntSet.empty cur) IntMap.empty [1..n]


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


