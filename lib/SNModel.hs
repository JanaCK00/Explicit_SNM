module SNModel where

--TODO only necessary imports
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , elements
  , sublistOf  )

import qualified Data.Map.Strict as M -- TODO do I need strict here?
import qualified Data.Set as S -- TODO do I need strict here?
import Data.Map.Strict ((!))
import Data.Set (Set)
import SetTheory

{-
Explicit representation of Social Network Models following Smets et al. (2020)
Relational Kripke models, per Def with
 - a non-empty, finite set of agents as the domain
 - a non-empty, finite set of topics
 - for each topic a non-empty, finite set of positions on the topic
There is a different social network for each topic.)
-}

{-
Social networks don't have to satisfy any properties
(i.e. they can be reflexive and non-symmetric).
-}

--TODO decide where to define this, once I have fixed the cyclic import issue with SetTheory
type Relation = M.Map Agent (Set Agent) --every agent should be a key


{-
TODO Is it enough to just assume that the sets and hence the maps will never be empty?
TODO do I even get a benefit from representing these as sets?? especially bc
I keep converting them to lists and back ;)
BUT: they might help me for uniqueness... (keys in Maps are unique anyways)
-}
data SNModel = SNM
 { agents :: Set Agent
 , positions :: M.Map Topic (Set Position)
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key
 , val :: M.Map Position (Set Agent) --the valuation, every position should be a key
 } deriving (Eq, Show)

{-
translation from val to dual.
  - can't have both as field in SNModel, bc it could get inconsistent
  - decided to have tuple as key, bc I never need the full set of positions of an agent

TODO look into caching when it's used several times
-}
agentPos :: SNModel -> M.Map (Agent, Topic) (Set Position)
agentPos (SNM agents' positions' _ val') = M.fromList[((ag, t), theirPs ag t)| ag <- S.toList agents', t <- M.keys positions'] where
    theirPs ag t = S.fromList [p | p <- S.toList $ positions' ! t, ag `S.member` (val' ! p)]

{-
Given a positions Map (M.Map Topic (Set Position)), returns a Set of all positions
-}
allPos :: M.Map Topic (Set Position) -> Set Position
allPos = S.unions . M.elems


{-
TODO would it make a difference to use Int instead of String?
With string I can make more readable examples
but in generation I only ever use "1", "2" a.s.o. anyway...
-}
newtype Agent = Ag String deriving (Eq, Show, Ord) --Set needs Ord, Map needs Ord for key
newtype Topic = Tpc String deriving (Eq, Show, Ord)
data Position = Pos { posTopic:: Topic, position :: String} deriving (Eq, Show, Ord)
    {-
    by having a field for the topic a position belongs to,
    I'm sure every position is unique across topics. (and I can always get out the topic)
    -}

--TODO do I benefit from using Set here?
--default Agents for usage in random generation
defaultAgents :: Set Agent
defaultAgents = S.fromList $ map (Ag . show) [(1::Int)..nrAgs] where
  nrAgs = 50 --CHANGE number of agents if needed



--defaultPositions for usage in random generation
defaultPositions :: M.Map Topic (Set Position)
defaultPositions = M.fromList [(t, ps t)| t <- map (Tpc . show) [(1::Int)..nrTpcs]] where
  nrTpcs = 30 --CHANGE number of topics if needed
  ps topic = S.fromList $ map (Pos topic . show) [(1::Int)..nrPos] where
    nrPos = 30 --CHANGE number of positions per topic if needed



{-
Arbitrary generation of Agents, Topics and Positions.
needed for random generation of formulas (see Syntax.hs)
(bc. agents, topics and positions show up in Propositions)

OR: would a defined defaultVocab be better? see Syntax.hs
-}

instance Arbitrary Agent where
  arbitrary = do setElements defaultAgents

instance Arbitrary Topic where
  arbitrary = do elements $ M.keys defaultPositions

instance Arbitrary Position where
  arbitrary = do setElements $ allPos defaultPositions


{-
some hardcoded examples
-}


alice, bob, carol, danny, emily :: Agent
alice = Ag "1"
bob = Ag "2"
carol = Ag "3"
danny = Ag "4"
emily = Ag "5"

books, games, sports :: Topic
books = Tpc "1"
games = Tpc "2"
sports = Tpc "3"


defaultTopics :: Set Topic
defaultTopics = S.fromList [books, games, sports]

fantasy, nonFiction, romance :: Position
fantasy = Pos books "1"
nonFiction = Pos books "2"
romance = Pos books "3"

booksPositions :: Set Position
booksPositions = S.fromList [fantasy, nonFiction, romance]

cardGames, boardGames, rolePlaying :: Position
cardGames = Pos games "1"
boardGames = Pos games "2"
rolePlaying = Pos games "3"

gamesPositions :: Set Position
gamesPositions = S.fromList [cardGames, boardGames, rolePlaying]

teamSports, running, weights :: Position
teamSports = Pos sports "1"
running = Pos sports "2"
weights = Pos sports "3"

sportsPositions :: Set Position
sportsPositions = S.fromList [teamSports, running, weights]

a, b, c, ab, ac, bc, abc :: Set Agent
a = S.singleton alice
b = S.singleton bob
c = S.singleton carol
ab = S.fromList [alice, bob]
ac = S.fromList [alice, carol]
bc = S.fromList [bob, carol]
abc = S.fromList [alice, bob, carol]

exampleSmall :: SNModel
exampleSmall = SNM abc positions' rel' val' where
    positions' = M.fromList [(books, booksPositions), (games, gamesPositions), (sports, sportsPositions)]
    rel' = M.fromList [(books, booksRel), (games, gamesRel), (sports, sportsRel)] where
        booksRel = M.fromList [(alice, abc),(bob, S.empty),(carol, ac)]
        gamesRel = M.fromList [(alice, S.empty), (bob, b),(carol, b)]
        sportsRel = M.fromList [(alice, ac), (bob, S.empty), (carol, a)]
    val' = M.fromList [(fantasy, ac), (romance, ab), (nonFiction, c), (cardGames, bc), (boardGames, c), (rolePlaying, S.empty), (teamSports, a), (running, ac), (weights, abc)]


{-
  Given a list of Agents, generate a random Relation (M.Map Agent (Set Agent))
  adapted from symbolic-topo-e-models.Explicit.kripkeModels

  TODO why did she use List here instead of set? To patternmatch more easily?
  but in the usage I have to convert defaultAgents to lists every time...
-}

randomRel :: [Agent] -> Gen Relation
randomRel [] = return M.empty
randomRel (ag:ags) = do
    thisAgsFriends <- M.singleton ag . S.fromList <$> sublistOf (ag:ags)
    rest <- randomRel ags
    return $ M.union rest thisAgsFriends

{-
  Given a list of agents and a list of topics, generates an arbitrary
  relation for each topic. This function applies randomRel to each topic.
  adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}
randomRelMap :: [Agent] -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap ags (t:tpcs) =  do
    thisTpcsRel <- M.singleton t <$> randomRel ags
    rest <- randomRelMap ags tpcs
    return $ M.union rest thisTpcsRel

{-
Given a list of agents and a list of positions, generate a random Valuation
-}
randomVal :: [Agent] -> [Position] -> Gen (M.Map Position (Set Agent))
randomVal _ [] = return M.empty
randomVal ags (p:pos) = do
    thisPosAgs <- M.singleton p . S.fromList <$> sublistOf ags
    rest <- randomVal ags pos
    return $ M.union rest thisPosAgs

{-
  Generate an arbitrary Social Network model.
    adapted from symbolic-topo-e-models.Explicit.kripkeModels
-}

instance Arbitrary SNModel where
  arbitrary = do
    --TODO limit some stuff?
    let ags = defaultAgents
        pos = defaultPositions
    randomRels <- randomRelMap (S.toList ags) (M.keys pos)
    randomV <- randomVal (S.toList ags) (S.toList $ allPos pos)
    return (SNM ags pos randomRels randomV)

--TODO is this the only way to generate in ghci?
getGenModel ::  Gen SNModel
getGenModel = arbitrary :: Gen SNModel

{-
usage in ghci:
import Test.QuickCheck
myModel <- generate getGenModel
-}


