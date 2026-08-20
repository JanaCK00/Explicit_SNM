{-# LANGUAGE TupleSections #-}

module SNModel where

import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S -- Set is strict ;)

import Data.Set (Set)
import qualified Data.IntSet as IntSet
import GenerationUtils
import Types
import qualified Data.Vector as V --vectors are 0-based!!
import Data.Vector (Vector)
import SMCDEL.Internal.Help (lfp)


{-
This module defines Social Networks Models.
It also provides random generation of Social Networks Models.
-}

--------------------------------------------------------------------------------
-- Definition of Social Networks Models
--------------------------------------------------------------------------------

{-
Social Networks Models are relational Kripke models, by definition with:

 - a non-empty, (finite) set of agents as the domain
 - a non-empty, (finite) set of topics
 - for each topic a non-empty, finite set of positions on the topic (These sets are pairwise disjoint.)
 - a binary relation for each topic (= social network).)
   (These don't have to satisfy any specific properties (such as symmetry or reflexivity).)
-}


{-
Social Networks Models are represented using the data type SNModel, consisting of the following fields:

- nrAgents:  An Int representing the number of Agents. It defines the set of agents ([0...nrAgents-1]).
- positions: A map from Topics to sets of Positions. It defines the set of topics and the corresponding sets of positions.
- rel:       A map from Topics to Relations. It defines the binary relation for each topic.
- dualVal:   A map from Topics to dual valuations (maps from Agents to sets of Positions).
             It defines the set of positions each agent has adopted for each topic.
            Agents that haven't adopted any position of a topic are omitted from the map.

SNModels are assumed to follow the definition of Social Networks Models specified above.
Additionally, the Topic (T 0) is reserved for internal use (see Semantics.hs).
These restrictions aren't enforced in construction, but should be checked using the function TODO
-}
data SNModel = SNM
 { nrAgents :: Int
 , positions :: M.Map Topic (Set Position)
 , rel :: M.Map Topic Relation
 , dualVal :: M.Map Topic (IntMap (Set Position))
 } deriving (Eq)



{-
For convenience, we provide a translation from the dual valuation to the valuation.
-}

{-
Input: SNModel
Output: Valuation corresponding to the dualVal
-}
val :: SNModel -> M.Map Topic (M.Map Position AgentSet)
val snm = M.fromList [(t, val_t snm t)| t <- topics] where
  topics = M.keys $ positions snm

{-
Input: SNModel, Topic
Output: Valuation for the given Topic
-}

--TODO test
--TODO I think positions that aren't taken by anyone won't be in the map at all
val_t :: SNModel -> Topic -> M.Map Position AgentSet
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
valToDualVal_t :: M.Map Position AgentSet -> IntMap (Set Position)
valToDualVal_t val_t' = IntMap.fromListWith S.union
    [ (i, S.singleton p)
    | (p, is) <- val_t_list
    , i <- IntSet.toList is
    ] where
  val_t_list = M.toList val_t'




{-
Checks if an SNModel is a valid Social Networks Model.
-}
isValidSNModel :: SNModel -> Bool
isValidSNModel snm = all fst $ isValidSNModelList snm


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


--Checks if the provided number is a valid nrAgents for an SNModel.
isValidnrAgents :: Int -> Bool
isValidnrAgents n = n > 0

--Checks if a provided map from Topics to Positions is a valid positions for an SNModel.
isValidpositions :: M.Map Topic (Set Position) -> Bool
isValidpositions pos = M.size pos > 0
  && (T 0) `M.notMember` pos
  && not (any null pos)
  && S.size (S.unions pos) == foldr ((+) . S.size) 0 pos




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
randomRelList :: Int -> Int -> Gen [AgentSet]
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
randomDualValT :: Set Position -> [Agent] -> Gen (IntMap (Set Position))
randomDualValT _ [] = return IntMap.empty
randomDualValT pos (ag:ags) = do
    thisAgsPos <- subsetOf pos
    rest <- randomDualValT pos ags
    if S.size thisAgsPos > 0 then --only include Agents in the map that take at least one position
      return $ IntMap.insert ag thisAgsPos rest
    else
      return rest


{-
Input:
posMap: positions map (Topic to Set of Positions)
ags: List of Agents

Output:
Applies randomDualValT for each topic and returns a randomly generated dualVal.
-}
randomDualValMap :: M.Map Topic (Set Position) -> [Agent] -> Gen (M.Map Topic (IntMap (Set Position)))
randomDualValMap posMap ags = traverse (`randomDualValT` ags) posMap



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
generate (getRandomSNModel 5 [(T 1, [P 1, P 2]), (T 2, [P 3, P 4])])

This example will generate a random SNModel with 5 agents and two topics having 2 positions each.
-}
getRandomSNModel :: Int -> [(Topic, [Position])] -> Gen SNModel
getRandomSNModel n tps = do
  let pos = M.map S.fromList $ M.fromList tps --make the input a Map
  if not (isValidnrAgents n)
    then error "Invalid number of agents. You need at least one agent."
    else if not (isValidpositions pos)
            then error "Invalid topics/positions. You need at least one topic (T 0 reserved), and for each topic at least one position. \n Positions can't belong to more than one topic."
            else do dualVal' <- randomDualValMap pos [0..n-1]
                    rel' <- randomRelMap n (M.keys pos)
                    return $ SNM n pos rel' dualVal'


{-
Default values for arbitrary generation. (defining the domain for Agents, Topics and Positions that can occur)
These are necessary to make sure arbitrary Forms match arbitrary SNModels.
-}
defaultNrAgs, nrTpcs, nrPosTotal :: Int
defaultNrAgs = 120
nrTpcs = 2
nrPosTotal = 6 --number of positions in total, assumes nrPosTotal >= nrTpcs

{-
  Generates an arbitrary SNModel based on the defined default values.
  The default values ensure that the arbitrary Forms match the arbitrary SNModels.
-}
instance Arbitrary SNModel where
  arbitrary = do
    let tpcs = map T [1..nrTpcs]
        pos = map P [1..nrPosTotal]
    randomTPMap <- randomPosMap tpcs pos
    randomRels <- randomRelMap defaultNrAgs tpcs
    randomDualVal <- randomDualValMap randomTPMap [0..defaultNrAgs-1]
    return (SNM defaultNrAgs randomTPMap randomRels randomDualVal)




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
    show snm = unlines
            [ ""
            , "SNModel"
            , ""
            , "Number of Agents: " ++ show (nrAgents snm)
            , ""
            , "Topics and Positions:"
            , showPositions (positions snm)
            , ""
            , "Relations:"
            , showRelations (rel snm)
            , ""
            , "Dual valuation:"
            , showDualVal (dualVal snm)
            ]
      where
        showPositions :: M.Map Topic (Set Position) -> String
        showPositions =
            unlines
            . map (\(t, ps) -> show t ++ ": " ++ show (S.toList ps))
            . M.toList

        showRelations :: M.Map Topic Relation -> String
        showRelations =
            unlines
            . map (\(t, r) -> show t ++ ":\n" ++ showRelation r)
            . M.toList

        showRelation :: Relation -> String
        showRelation r =
            unlines
                [ show i ++ ": " ++ show (IntSet.toList neighbours)
                | (i, neighbours) <- zip [0..] (V.toList r)
                ]

        showDualVal :: M.Map Topic (IntMap (Set Position)) -> String
        showDualVal =
            unlines
            . map (\(t, d) -> show t ++ ":\n" ++ showDualVal_t d)
            . M.toList

        showDualVal_t :: IntMap (Set Position) -> String
        showDualVal_t d =
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


