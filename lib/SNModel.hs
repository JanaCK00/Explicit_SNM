module SNModel where

--TODO only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , elements
  , sublistOf  )
import Test.QuickCheck.Gen (chooseInt)
import qualified Data.Map.Strict as M
import qualified Data.Set as S -- Set is strict ;)
--import Data.Map.Strict ((!))
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import SetTheory

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
-- TODO LOOK UP : can I use IntMaps? are they good
--TODO change to have dual here
data SNModel = SNM
 { agents :: AgentSet --TODO ?maybe have this as a list, bc I don't check for membership here, but rather can use it in recursion in update functions??
 , positions :: M.Map Topic (Set Position) --pariwise disjoint sets. this could actually also be a map of sizes and then have the topic in the position like i planned originally...and you only need the list of positions for a topic to go through for the annpying case of Infl 0...
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key
 , val :: M.Map Position AgentSet --the valuation, every position should be a key
 } deriving (Eq, Show)



{-
translation from val to dual.
  - can't have both as field in SNModel, bc it could get inconsistent
  - decided to have tuple as key, bc I never need the full set of positions of an agent

TODO look into caching when it's used several times
PROBLEM, it changes when positions change! And it's super expensive to compute.
Also I think it's not necessary :)
-}
--agentPos :: SNModel -> M.Map (Agent, Topic) (Set Position)
--agentPos (SNM agents' positions' _ val') = M.fromList[((ag, t), theirPs ag t)| ag <- S.toList agents', t <- M.keys positions'] where
    --theirPs ag t = S.fromList [p | p <- S.toList $ positions' ! t, ag `S.member` (val' ! p)]

{-
Given a positions Map (M.Map Topic (Set Position)), returns a Set of all positions
used for arbitrary generation of positions based on the default positions map
-}
allPos :: M.Map Topic (Set Position) -> Set Position
allPos = S.unions
{-
TODO alternatively I could make the function from SNModel and use M.keys(Set) val
-}

--definitions for Agent/Relation in SetTheory.hs

newtype Topic = T Int deriving (Eq, Show, Ord)  --Set needs Ord, Map needs Ord for key
newtype Position = P Int deriving (Eq, Show, Ord)


--CHANGE default values if neded
nrAgs, nrTpcs, nrPosPerT, nrPosTotal :: Int
nrAgs = 50
nrTpcs = 10
nrPosPerT = 10 --number of positions per Topic, TODO go change this where it's used TODO is it ok if it can't generate more variety in the nr of pos?
nrPosTotal = 100 --number of positions in total, nrPosTotal >= nrTpcs TODO just trying if this works

--default Agents for usage in random generation
defaultAgents :: AgentSet
defaultAgents = IntSet.fromList [1..nrAgs]

--TODO change where this is used
--default Positions for usage in random generation
--make sure the positions are different across topics
defaultPositions :: M.Map Topic (Set Position)
defaultPositions =  M.fromList [ (T t, S.fromList [P p | p <- [(t-1)*nrPosPerT + 1 .. t*nrPosPerT]])| t <- [1..nrTpcs]]


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
exampleSmall = SNM abc positions' rel' val' where
    positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
    rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = M.fromList [(alice, abc),(bob, IntSet.empty),(carol, ac)]
        gamesRel = M.fromList [(alice, IntSet.empty), (bob, b),(carol, b)]
        sportsRel = M.fromList [(alice, ac), (bob, IntSet.empty), (carol, a)]
    val' = M.fromList [(fantasy, ac), (romance, ab), (nonFiction, c), (cardGames, bc), (boardGames, c), (rolePlaying, IntSet.empty), (teamSports, a), (running, ac), (weights, abc)]


--TODO bit of a boring example, it's for simple testing of the settheory stuff
exampleCircleFriendship :: SNModel
exampleCircleFriendship = SNM group positions' rel' val' where
  group = IntSet.fromList [alice, bob, carol, danny]
  positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
  rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = M.fromList [(alice, b),(bob, c),(carol, d), (danny,a)]
        gamesRel = M.fromList [(alice, b),(bob, c),(carol, d), (danny,a)]
        sportsRel = M.fromList [(alice, b),(bob, c),(carol, d), (danny,a)]
  val' = M.fromList [(fantasy, ac), (romance, ab), (nonFiction, c), (cardGames, bc), (boardGames, c), (rolePlaying, IntSet.empty), (teamSports, a), (running, ac), (weights, abc)]




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
randomRel _ [] = return M.empty
randomRel allAgs (ag:ags) = do
    thisAgsFriends <- IntSet.fromList <$> sublistOf allAgs
    rest <- randomRel allAgs ags
    return $ M.insert ag thisAgsFriends rest

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
Given a list of agents and a list of positions (both duplicate-free), generate a random Valuation
-}
randomVal :: [Agent] -> [Position] -> Gen (M.Map Position AgentSet)
randomVal _ [] = return M.empty
randomVal ags (p:pos) = do
    thisPosAgs <- IntSet.fromList <$> sublistOf ags
    rest <- randomVal ags pos
    return $ M.insert p thisPosAgs rest

{-
  Generate an arbitrary Social Network model.
    adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}


--TODO decide if topics with just one positions even make sense...
--assumes length list >= Int
--takes an Int and a list. generates a partition with exactly Int number of  non-empty subsets
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
generate a mapping from topics to sets of positions (pariwise disjoint, non-empty)
-}
randomPosMap :: [Topic] -> [Position] -> Gen (M.Map Topic (Set Position))
randomPosMap ts ps = do
  partition <- randomPart (length ts) ps
  return $ M.fromList $ zipWith (\t partP -> (t, S.fromList partP)) ts partition



instance Arbitrary SNModel where
  arbitrary = do
    --TODO limit some stuff? (not necessary, bc I don't close under reflexivity/transitivity?)
    let ags = [1..nrAgs]
        tpcs = map T [1..nrTpcs]
        pos = map P [1..nrPosTotal]
    randomTPMap <- randomPosMap tpcs pos
    randomRels <- randomRelMap ags tpcs
    randomV <- randomVal ags pos
    return (SNM defaultAgents randomTPMap randomRels randomV)

{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel
-}


