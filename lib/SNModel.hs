module SNModel where

--TODO add necessary imports
import qualified Data.Map.Strict as M -- TODO do I need strict here?
import qualified Data.Set as S -- TODO shold I restrict the function I import here?
import Data.Map.Strict ((!)) -- so I can use it wihtout M.
import Data.Set (Set)        --so I can use it witout S.
import Test.QuickCheck.Monadic (run)

{-
Explicit representation of Social Network Models following Smets et al. (2020)
Relational Kripke models, per Def with
 - a non-empty, finite set agents as the domain
 - a non-empty, finite set of topics
 - for each topic a non-empty, finite set of positions on the topic
There is a different social network for each topic.)
-}


{-
Social networks don't have to satisfy any properties
(i.e. they can be reflexive and non-symmetric).
-}


--TODO decide whether to import this from SetTheory, once it's fixed there
--ACHTUNG das hat die ganzen Fehler produziert
type Relation = M.Map Agent (Set Agent)


--Is it enough to just assume that the sets and hence the maps will never be empty?
--do I even get a benefit from representing these as sets??
--especially bc I keep converting them to lists and back ;)
--BUT: they might help me for the uniqueness...
data SNModel = SNM
 { agents :: Set Agent
 --, topics :: Set Topic --TODO do I even need this, if I have the maps? I can get it from M.keysSet positions
 , positions :: M.Map Topic (Set Position) -- or is the other way round better and then I don't need the topic in the data type?
 , rel :: M.Map Topic Relation --the social networks. I want this to be from all topics, and in the relations from all agents
 , val :: M.Map Position (Set Agent) --TODO this is valuation, should have all Positions as keys (maybe sometimes maps to empty set)
 } --TODO deriving stuff?

{-
translation from val to dual.
Like this is doesn't get inconsistent, and if i need it several times I could cache it...
    -}
agentPos :: SNModel -> M.Map (Agent, Topic) (Set Position) --I prefer tuple -> set to a nested map I think, bc I never need all the positions, only ever topic specific
agentPos (SNM agents' positions' _ val') = M.fromList[((ag, t), theirPs ag t)| ag <- S.toList agents', t <- S.toList $ M.keysSet positions'] where
    theirPs ag t = S.fromList [p | p <- S.toList $ positions' ! t, ag `S.member` (val' ! p)]

--TODO necessary?
allPos :: M.Map Topic (Set Position) -> Set Position
allPos = S.unions . M.elems


--ACHTUNG Set braucht Ord!! Map braucht bei key Ord
newtype Agent = Ag String deriving (Eq, Show, Ord)
newtype Topic = Tpc String deriving (Eq, Show, Ord)
data Position = Pos { posTopic:: Topic, position :: String} deriving (Eq, Show, Ord)
    --like this I'm sure they never intersect!..and I can always get out the topic
    --or could it be avoided somehow?
--TODO do I need to make sure, these are always different from each other?? Or do the sets help me there?
--sould I use type or newtype? Should I use String or Int?
--TODO do I need to get the string out there sometimes? Probabily not, right?



{-
some hardcoded examples
-}


alice, bob, carol, danny, emily :: Agent
alice = Ag "1"
bob = Ag "1"
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

teamSports, running, weights :: Position
teamSports = Pos sports "1"
running = Pos sports "2"
weights = Pos sports "3"

sportsPositions :: Set Position
sportsPositions = S.fromList [teamSports, running, weights]

cardGames, boardGames, rolePlaying :: Position
cardGames = Pos games "1"
boardGames = Pos games "2"
rolePlaying = Pos games "3"

gamesPositions :: Set Position
gamesPositions = S.fromList [cardGames, boardGames, rolePlaying]

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


--TODO randomly generate models





