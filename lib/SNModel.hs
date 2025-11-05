{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module SNModel where

--TODO only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , elements
  , sublistOf  )

import qualified Data.Map.Strict as M -- TODO do I need strict here?
import qualified Data.Set as S -- TODO do I need strict here?
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

--TODO decide where to define this, once I have fixed the cyclic import issue with SetTheory
--put it in SetTheory for now
--type AgentSet = IntSet
--type Relation = M.Map Agent IntSet --every agent should be a key


{-
All sets/maps should by def be non-empty. This isn't enforced, but
TODO check validity of model before checking formulas
-}
-- LOOK UP : can I use IntMaps? are they good
data SNModel = SNM
 { agents :: AgentSet
 , positions :: M.Map Topic (Set Position) --the sets should be pairwise disjoint -- ? TODO I could combine this with the val map...
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


{-
  IDEA just have strings for Agent
  T 1 , P 1
  maybe have agents just integer, otherwise use monad to map over wrappers
  Topic and Positions have Ints
  IDEA newtype is bad, use data instead
-}
--type Agent = Int -- put it in SetTheory for now
data Topic = T Int deriving (Eq, Show, Ord)  --Set needs Ord, Map needs Ord for key

--IDEA assume positions are different (disjoint sets) and then don't include the topic here
--if there would be two that are the same, you can manually double it,
--MAKE SURE it works in arbitrary generation!!
data Position = P Int deriving (Eq, Show, Ord)


--default Agents for usage in random generation
defaultAgents :: AgentSet
defaultAgents = IntSet.fromList [1..nrAgs] where
  nrAgs = 50 --CHANGE number of agents if needed



--defaultPositions for usage in random generation
--make sure the positions are different across topics
defaultPositions :: M.Map Topic (Set Position)
defaultPositions =  M.fromList [ (T t, S.fromList [P p | p <- [(t-1)*nrPos + 1 .. t*nrPos]])| t <- [1..nrTpcs]] where
  nrTpcs = 10 --CHANGE number of topics if needed
  nrPos  = 10 --CHANGE number of positions per topic if needed

{-
Arbitrary generation of Agents, Topics and Positions.
needed for random generation of formulas (see Syntax.hs)
(bc. agents, topics and positions show up in Propositions)

OR: would a defined defaultVocab be better? see Syntax.hs
-}


instance Arbitrary Topic where
  arbitrary = do elements $ M.keys defaultPositions

instance Arbitrary Position where
  arbitrary = do setElements $ allPos defaultPositions   --TODO List Conversion in setElements --TODO computes allPos everytime!!!


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
 TODO why did she use List here instead of set? Is it because impure stuff that can't handle folds?
 and also: I think a one time conversion from Set Agent to [Agent] is better than using subsetOf in a fold anyway
 bc. it uses to List and from list everytime

  Given a list of Agents, generate a random Relation (M.Map Agent (Set Agent))
  adapted from symbolic-topo-e-models.Explicit.kripkeModels


-}

--IDEA make sure that positions are different (without having the topic in the data)
--ACHTUNG ich glaube, das hat vorher nicht funktionier!! weil ich keine symmetrischen Relationen habe
--probierter fix: die erste Liste wird unverändert weitergereicht, die zweite ist das rekurive element
randomRel :: [Agent] -> [Agent] -> Gen Relation
randomRel _ [] = return M.empty
randomRel allAgs (ag:ags) = do
    thisAgsFriends <- M.singleton ag . IntSet.fromList <$> sublistOf allAgs
    rest <- randomRel allAgs ags
    return $ M.union rest thisAgsFriends

{-
  Given a list of agents and a list of topics, generates an arbitrary
  relation for each topic. This function applies randomRel to each topic.
  adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}
randomRelMap :: [Agent] -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap ags (t:tpcs) =  do
    thisTpcsRel <- M.singleton t <$> randomRel ags ags
    rest <- randomRelMap ags tpcs
    return $ M.union rest thisTpcsRel

{-
Given a list of agents and a list of positions, generate a random Valuation
-}
randomVal :: [Agent] -> [Position] -> Gen (M.Map Position AgentSet)
randomVal _ [] = return M.empty
randomVal ags (p:pos) = do
    thisPosAgs <- M.singleton p . IntSet.fromList <$> sublistOf ags
    rest <- randomVal ags pos
    return $ M.union rest thisPosAgs

{-
  Generate an arbitrary Social Network model.
    adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}

instance Arbitrary SNModel where
  arbitrary = do
    --TODO limit some stuff? but it's less necessary, bc I dont do close it under reflexivity and transitivity
    let ags = defaultAgents
        pos = defaultPositions
    randomRels <- randomRelMap (IntSet.toList ags) (M.keys pos) --TODO list conversion
    randomV <- randomVal (IntSet.toList ags) (S.toList $ allPos pos)
    return (SNM ags pos randomRels randomV)

--TODO is this the only way to generate in ghci?
getGenModel ::  Gen SNModel
getGenModel = arbitrary :: Gen SNModel

{-
usage in ghci:
import Test.QuickCheck
myModel <- generate getGenModel
-}


