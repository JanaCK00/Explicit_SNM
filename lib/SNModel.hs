module SNModel where

--TODO add necessary imports
import qualified Data.Map.Strict as M -- TODO do I need strict here?
import qualified Data.Set as S -- TODO shold I restrict the function I import here?
import Data.Map.Strict ((!)) -- so I can use it wihtout M.
import Data.Set (Set)        --so I can use it witout S.

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
data SNModel = SNM
 { agents :: Set Agent
 , topics :: Set Topic --TODO do I even need this, if I have the maps?
 , positions :: M.Map Topic (Set Position) -- or is the other way round better and then I don't need the topic in the data type?
 , rel :: M.Map Topic Relation --the social networks. I want this to be from all topics, and in the relations from all agents
 , val :: M.Map Position (Set Agent) --TODO this is valuation, should have all Positions as keys (maybe sometimes maps to empty set)
 } --TODO deriving stuff?

{-
TODO write a translation from val to pos (dual)? Like this is doesn't get inconsistent
if i need the same pos several times I could cache it...
    -}
--pos :: SNModel -> M.Map (Agent, Topic) (Set Position)
--pos SNM agents _ positions _ val =

--ACHTUNG Set braucht Ord!! Map braucht bei key Ord
newtype Agent = Ag String deriving (Eq, Show, Ord)
newtype Topic = Tpc String deriving (Eq, Show, Ord)
data Position = Pos Topic String deriving (Eq, Show, Ord)
    --like this I'm sure they never intersect..and I can always get out the topic
    --but it might need a lot of space and maybe it can be avoided?
--TODO do I need to make sure, these are always different from each other?? Or do the sets help me there?
--sould I use type or newtype? Should I use String or Int?
--TODO do I need to get the string out there sometimes? Probabily not, right?

--TODO wie sorge ich dafür, dass all die Sets nicht leer sind?



{-
TODO hardcoding some examples
-}

--TODO how to do this usefully?

alice, bob, carol, danny, emily :: Agent
alice = Ag "Alice"
bob = Ag "Bob"
carol = Ag "Carol"
danny = Ag "Danny"
emily = Ag "Emily"


defaultAgentsBig :: Set Agent
defaultAgentsBig = S.fromList [alice, bob, carol, danny, emily]


books, sports, games :: Topic
books = Tpc "Books"
sports = Tpc "Sports"
games = Tpc "Games"

defaultTopics :: Set Topic
defaultTopics = S.fromList [books, sports, games]

fantasy, nonFiction, romance :: Position
fantasy = Pos books "Fantasy"
nonFiction = Pos books "Non-fiction"
romance = Pos books "Romance"

booksPositions :: Set Position
booksPositions = S.fromList [fantasy, nonFiction, romance]

teamSports, running :: Position
teamSports = Pos sports "Team Sports"
running = Pos sports "Running"

sportsPositions :: Set Position
sportsPositions = S.fromList [teamSports, running]

cardGames, boardGames :: Position
cardGames = Pos games "Card Games"
boardGames = Pos games "Board Games"

gamesPositions :: Set Position
gamesPositions = S.fromList [cardGames, boardGames]

a, b, c, ab, ac, bc, abc :: Set Agent
a = S.singleton alice
b = S.singleton bob
c = S.singleton carol
ab = S.fromList [alice, bob]
ac = S.fromList [alice, carol]
bc = S.fromList [bob, carol]
abc = S.fromList [alice, bob, carol]

exampleSmall :: SNModel
exampleSmall = SNM abc topics' positions' rel' val' where
    topics' = S.fromList [books, games]
    positions' = M.fromList [(books, booksPositions), (games, gamesPositions)]
    rel' = M.fromList [(books, booksRel), (games, gamesRel)] where
        booksRel = M.fromList [(alice, abc),(bob, S.empty),(carol, ac)]
        gamesRel = M.fromList [(alice, S.empty), (bob, b),(carol, b)]
    val' = M.fromList [(fantasy, ac), (romance, ab), (nonFiction, c), (cardGames, bc), (boardGames, c)]







