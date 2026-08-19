{-# LANGUAGE TupleSections #-}

module SNModel where

import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf)
import Test.QuickCheck.Gen (chooseInt)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S -- Set is strict ;)

import Data.Set (Set)
import qualified Data.IntSet as IntSet
import SetTheory
import qualified Data.Vector as V

{-
Explicit representation of Social Networks Models following Smets et al. (2020)
Relational Kripke models, by definition with
 - a non-empty, (finite) set of agents as the domain
 - a non-empty, (finite) set of topics
 - for each topic a non-empty, finite set of positions on the topic. These sets are pairwise disjoint.
 - a binary relation for each topic (= social network).)

Assumptions on the form of SNM: (that aren't enforced here, but should be checked before working with a model)

(1) All sets/maps should by def be non-empty. (except IntMap (Set Positions), that can be empty )
(2) The sets of Positions are pairwise disjoint across topics. TODO manually double them when a provided model violates this.
(3) The maps contain every topic of the model as a key. Dual_t only contains agents as keys who have non-empty set of positions in that topic
-}

--no friends is very rare -> vector
--no position is NOT rare -> Map

data SNModel = SNM
 { nrAgents :: Int --agents are referred to by 0 .. (nrAgents - 1)
 , positions :: M.Map Topic (Set Position) --pairwise disjoint sets ACHTUNG TODO : TOPICS CAN NOT INCLUDE (T 0), that's a special case reserved for internal use!
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key. Social networks don't have to satisfy any properties
 , dualVal :: M.Map Topic (IntMap (Set Position)) --every topic should be a key, but only agents taking more than 0 positions are keys (bc no position taken is also quite common)
 } deriving (Eq)



isValidSNModelList :: SNModel -> [(Bool, String)]
isValidSNModelList (SNM ags' pos' rel' dualVal') =
  [ (isValidnrAgents ags' , "Invalid number of agents. You need at least one agent.")
  , (isValidpositions pos', "Invalid topics/positions. You need at least one topic (T 0 reserved), and for each topic at least one position. \n Positions can't belong to more than one topic.")
  , (M.keys pos' == M.keys rel' && M.keys pos' == M.keys dualVal', "Not valid. Your topics aren't consistent across maps.")
  , (allWithKey (\t iPs -> all (`S.isSubsetOf` (pos' M.! t)) iPs) dualVal', "Not valid. Your dualVal valuation assigns positions that aren't consistent with the Topics/Positions map.")
  , (not (any (any null) dualVal'), "Not valid. Agents that don't adopt any positions in a topic shouldn't be keys in the dualVal_t map.")
  , (all (\v -> V.length v == ags') rel', "Not valid. Not all of your relations have the right size.")
  , (all (all (allElems (<= ags'))) rel', "Not valid. Your relations contain agents that don't exist.")
  , (all (\m -> maximum (IntMap.keys m) <= ags') dualVal', "Not valid. Your dualVal valuation contains agents that don't exist.")
  ]
  where
    allElems predicate ks = all predicate (IntSet.toList ks)
    allWithKey predicate = M.foldrWithKey (\k v acc -> predicate k v && acc) True

isValidSNModel :: SNModel -> Bool
isValidSNModel snm = all fst $ isValidSNModelList snm

isValidnrAgents :: Int -> Bool
isValidnrAgents n = n > 0

isValidpositions :: M.Map Topic (Set Position) -> Bool
isValidpositions pos = M.size pos > 0
  && (T 0) `M.notMember` pos
  && not (any null pos)
  && S.size (S.unions pos) == foldr ((+) . S.size) 0 pos

--See definitions for Agent/Relation in SetTheory.hs

newtype Topic = T Int deriving (Eq, Show, Ord) --T 0 is reserved for internal use
newtype Position = P Int deriving (Eq, Show, Ord)




{-
Input: SNModel
Output: Valuation corresponding to the dualVal
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
    | (i, ps) <- dualVal_t_list
    , p <- S.toList ps
    ] where
  dualVal_t = dualVal snm M.! t
  dualVal_t_list =  IntMap.toList dualVal_t


--TODO test
{-
Input: Valuation for a specific topic.
Output: Corresponding dualVal for that topic.
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
Functions for random generation of components of SNModels.
They use Lists instead of Sets for convenience, and because the sublist function would require list conversion anyway.
-}


{-
Input:
nrAgs: Stands for agents [0..nrAgs-1].

Output:
Generates a random Relation between agents [0..nrAgs-1].
-}
randomRel :: Int -> Gen Relation
randomRel nrAgs = do
  list <- randomRelList nrAgs nrAgs
  return $ V.fromList list

--second argument is the recursively decreasing one
randomRelList :: Int -> Int -> Gen [IntSet.IntSet]
randomRelList _ 0 = return []
randomRelList nrAgs n = do
    thisAgsFriends <- IntSet.fromList <$> sublistOf [0..nrAgs-1]
    rest <- randomRelList nrAgs (n-1)
    return $ thisAgsFriends:rest


{-
Input:
nrAgs: Stands for agents [0..nrAgs-1].
tpcs: List of Topics (duplicate-free)

Output:
Generates an random relation for each topic and returns the corresponding map.
-}
randomRelMap :: Int -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap nrAgs (t:tpcs) =  do
    thisTpcsRel <- randomRel nrAgs
    rest <- randomRelMap nrAgs tpcs
    return $ M.insert t thisTpcsRel rest


{-
Input:
pos: Set of Positions (assumed to belong to one topic)
ags: List of Agents (duplicate free)

Output:
Generates a random dualVal for one topic (Map from Agent to subset of those Positions) and returns the corresponding map.
-}
randomDualT :: Set Position -> [Agent] -> Gen (IntMap (Set Position))
randomDualT _ [] = return IntMap.empty
randomDualT pos (ag:ags) = do
    thisAgsPos <- subsetOf pos
    rest <- randomDualT pos ags
    if S.size thisAgsPos > 0 then --only include Agents in the map that take at least one position
      return $ IntMap.insert ag thisAgsPos rest
    else
      return rest


{-
Input:
posMap: positions map (Topic to Set of Positions)
ags: List of Agents

Output:
Applies randomDualT for each topic and returns a randomly generated dualVal.
-}
randomDualMap :: M.Map Topic (Set Position) -> [Agent] -> Gen (M.Map Topic (IntMap (Set Position)))
randomDualMap posMap ags = traverse (`randomDualT` ags) posMap

{-
Input:
l: number of partitions > 0
xs: list
(Assumptions: length xs >= l)

Output:
Generates a partition of xs with exactly l non-empty subsets.
-}
randomPart :: Int -> [a] -> Gen [[a]]
randomPart 1 xs = return [xs]
randomPart l xs = do
  let n = length xs
  thisLength <- chooseInt (1, n - l + 1) --make sure the rest of the (l-1) partitions still get at least one element each
  let (first, rest) = splitAt thisLength xs
  restPart <- randomPart (l-1) rest
  return $ first : restPart


{-
Input:
ts: List of Topics
ps: List of Positions
(Assumptions: both duplicate free & non-empty, length ps>=length ts)

Output:
Generates a mapping from topics to sets of positions (pairwise disjoint, non-empty).
-}
randomPosMap :: [Topic] -> [Position] -> Gen (M.Map Topic (Set Position))
randomPosMap ts ps = do
  partition <- randomPart (length ts) ps
  return $ M.fromList $ zipWith (\t partP -> (t, S.fromList partP)) ts partition




{-
Random generation of SNModels.
-}


{-
Input:
n: number of agents
tps: a list of tuples (Topic, [Position])

Output:
Returns a randomly generated SNmodel if the input is valid.

Example input in ghci:
import Test.QuickCheck
generate (getRandomSNModel 5 [(T 1, [P 1, P 2]), (T 2, [P 3, P 4])]

This will generate a random SNModel with 5 agents and two topics having 2 positions each.
-}
getRandomSNModel :: Int -> [(Topic, [Position])] -> Gen SNModel
getRandomSNModel n tps = do
  let pos = M.map S.fromList $ M.fromList tps --make the input a Map
  if not (isValidnrAgents n)
    then error "Invalid number of agents. You need at least one agent."
    else if not (isValidpositions pos)
            then error "Invalid topics/positions. You need at least one topic (T 0 reserved), and for each topic at least one position. \n Positions can't belong to more than one topic."
            else do dualVal' <- randomDualMap pos [0..n-1]
                    rel' <- randomRelMap n (M.keys pos)
                    return $ SNM n pos rel' dualVal'



--CHANGE default values for arbitrary generation if needed
defaultNrAgs, nrTpcs, nrPosTotal :: Int
defaultNrAgs = 120
nrTpcs = 2
nrPosTotal = 6 --number of positions in total, make sure nrPosTotal >= nrTpcs

{-
  Generates an arbitrary SNModel based on the defined default values.
  The default values are necessary to make sure the arbitrary Forms match the arbitrary SNModels.
-}
instance Arbitrary SNModel where
  arbitrary = do
    let tpcs = map T [1..nrTpcs] --fixed for formula generation purposes
        pos = map P [1..nrPosTotal] --fixed for formula generation purposes
    randomTPMap <- randomPosMap tpcs pos
    randomRels <- randomRelMap defaultNrAgs tpcs
    randomDual <- randomDualMap randomTPMap [0..defaultNrAgs-1]
    return (SNM defaultNrAgs randomTPMap randomRels randomDual)




{-
Takes a SNModel and makes full relations for all topics.
Used in Semantics.hs for Selec Basic 0.
-}
makeFullRelModel :: SNModel -> SNModel
makeFullRelModel m@(SNM nrAgents' pos' _ _) = m { rel = fullRels } where
    fullRels = M.fromList $ map (, fullRel) (M.keys pos')
    fullRel = makeFullRel nrAgents'


makeFullRel :: Int -> Relation
makeFullRel n = V.replicate n $ IntSet.fromList [0..(n-1)]

{-
Takes a number of agents and creates an empty Relation.
Can be used for SNModel construction.
-}
makeEmptyRel :: Int -> Relation
makeEmptyRel n = V.replicate n IntSet.empty

{-
Takes a SNModel and makes all its relations reflexive.
Can be used for SNModel construction.
Is currently used in testing.
-}
makeReflModel :: SNModel -> SNModel
makeReflModel m@(SNM _ _ rel' _) = m {rel = M.map makeReflexive rel'}

{-
Takes a SNmodel and makes all its relations symmetric.
Can be used for SNModel construction.
Is currently used in testing.
-}
makeSymModel :: SNModel -> SNModel
makeSymModel m@(SNM _ _ rel' _) = m {rel = M.map makeSymmetric rel'}


--TODO Achtung . - .
--Makes SNModels more readable in the console (works especially for smaller models).
instance Show SNModel where
    show snm =
        unlines
            [ ""
            , "SNModel"
            , ""
            , "Number of Agents: " ++ show (nrAgents snm)
            , ""
            , "Topics and Positions:"
            , showMap (positions snm)
            , ""
            , "Relations:"
            , showMapWith showRelation (rel snm)
            , ""
            , "Dual valuation:"
            , showMapWith showDual (dualVal snm)
            ]
      where
        showMap :: M.Map Topic (Set Position) -> String
        showMap =
            unlines
            . map (\(t, ps) -> show t ++ ": " ++ show (S.toList ps))
            . M.toList

        showMapWith :: Show k
                    => (v -> String)
                    -> M.Map k v
                    -> String
        showMapWith showValue =
            unlines
            . map (\(k, v) -> show k ++ ":\n" ++ showValue v)
            . M.toList

        showRelation :: Relation -> String
        showRelation r =
            unlines
                [ show i ++ ": " ++ show (IntSet.toList neighbours)
                | (i, neighbours) <- zip [0..] (V.toList r)
                ]

        showDual :: IntMap (Set Position) -> String
        showDual d =
            unlines
                [ show ag ++ ": " ++ show (S.toList ps)
                | (ag, ps) <- IntMap.toList d
                ]


{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel
generate (randomRel 4)
-}


