module Semantics where


import Syntax (Form(..), Mode(..), isInUpdateModeCons, simplify, getAgs, getTops, getPos, validTaus, validTau)
import SNModel (SNModel(rel, dualVal, SNM, nrAgents, positions), makeFullRelModel, isWellFormedSNModel)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import qualified Data.Matrix as Mat --Rows and columns are indexed starting with 1.
import Data.Matrix (Matrix)
import qualified Data.Vector as V --Vectors are indexed starting with 0.
import Data.Vector (Vector)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as L
import Types


{-
This modules implements the semantics as defined by Smets et al. (2020).

It contains update functions for basic social influence and friendship selection,
as well as for extended social influence and restricted friendship selection.
-}



--------------------------------------------------------------------------------
-- Model checking
--------------------------------------------------------------------------------


{-
Validation-wrapped model checking function.

Input:
snm: SNModel
f: Form

Output:
Checks if f ise mode consistent.
Cheks if f only contains valid thresholds (in [0,1]).
Checks if snm is a well-formed social networks model.
Checks if Agents, Topics and Positions occurring in f also appear in snm.

In case of violations, terminated with descriptive error message.

If all conditions hold, checks if f holds on snm.


Example usage in ghci:
import Test.QuickCheck
myModel <- generate $ (getRandomSNModel 5 [(T 1, [P 1, P 2]), (T 2, [P 3, P 4])])
myForm <- generate $  getRandomFormModel Basic myModel
myModel *|= myForm
-}

(*|=) :: SNModel -> Form -> Bool
(*|=) snm f | not (isInUpdateModeCons f) = error "Formula is not mode-consistent."
            | not (validTaus f')         = error "Formula contains modal operators with invalid thresholds (not in [0,1])."
            | not wellFormedSNM          = error $ "Social Networks Model is not well-formed. \n" ++ unlines errorList
            | not (match snm f')         = error "Formula contains Agents, Topics or Positions that aren't defined in the Social Networks Model."
            | otherwise                  = snm |= f'
        where f' = simplify f
              (wellFormedSNM, errorList) = isWellFormedSNModel snm



{-
Input:
snm: SNModel
f: Form

Checks if Agents, Topics and Positions occurring in f are all defined in snm and hence
f can be checked on snm.
-}
match :: SNModel -> Form -> Bool
match snm f = matchAg && matchTops && matchPos where
    matchAg | null ourAgs = True
            | otherwise = maximum ourAgs <= nrAgents snm
            where ourAgs = IntSet.toList $ getAgs f
    matchTops = getTops f `S.isSubsetOf` M.keysSet (positions snm)
    matchPos = getPos f `S.isSubsetOf` M.foldr S.union S.empty (positions snm)



{-
Unsafe model checking function.
! Assumes a well-formed SNModel, and a well-formed and matching Form.
! Doesn't simplify the Form before checking.

Best used with an already simplified Form, to avoid expensive update computation.
-}
(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (Adopted agent position')                = any ((position' `S.member`) . lookupDualVal agent) (dualVal m)
(|=) m (Connected topic agent1 agent2)          = agent2 `IntSet.member`((rel m ! topic) V.! agent1)
(|=) m (Neg f)                                  = not $ m |= f
(|=) m (Conj fs)                                = all (m |=) fs --returns true on empty list
(|=) m (Disj fs)                                = any (m |=) fs --returns false on an empty list
(|=) m (Impl f g)                               = not (m |= f) || m |= g

(|=) m (Infl Basic tau f)                       = (|=) (updInflBasic tau m) f --Basic: Social Influence
(|=) m (Selec Basic tau f)                      = (|=) (updSelecBasic tau m) f --Basic: Friendship Selection

(|=) m (Infl Variant tau f)                     = (|=) (updInflVariant tau m) f --Variant: Extended Social Influence
(|=) m (Selec Variant tau f)                    = (|=) (updSelecVariant tau m) f --Variant: Restricted Friendship Selection





--------------------------------------------------------------------------------
-- Validation-wrapped update functions
--------------------------------------------------------------------------------

{-
The following functions are validation-wrappers around the update functions.
They check whether the input is admissible before calling the respective update functions.
-}

validInflBasic :: Double -> SNModel -> SNModel
validInflBasic  tau snm | not $ validTau tau = error "Invalid threshold. Thresholds must be in [0,1]."
                         | not wellFormedSNM  = error $ "Social Networks Model is not well-formed. \n" ++ unlines errorList
                         | otherwise          = updInflBasic tau snm
        where
            (wellFormedSNM, errorList) = isWellFormedSNModel snm


validSelecBasic ::  Double -> SNModel -> SNModel
validSelecBasic tau snm | not $ validTau tau = error "Invalid threshold. Thresholds must be in [0,1]."
                          | not wellFormedSNM  = error $ "Social Networks Model is not well-formed. \n" ++ unlines errorList
                          | otherwise          = updSelecBasic tau snm
        where
            (wellFormedSNM, errorList) = isWellFormedSNModel snm


validInflVariant :: Double -> SNModel -> SNModel
validInflVariant tau snm |  not $ validTau tau = error "Invalid threshold. Thresholds must be in [0,1]."
                           | not wellFormedSNM   = error $ "Social Networks Model is not well-formed. \n" ++ unlines errorList
                           | otherwise           = updInflVariant tau snm
        where
            (wellFormedSNM, errorList) = isWellFormedSNModel snm


validSelecVariant :: Double -> SNModel -> SNModel
validSelecVariant tau snm |not $ validTau tau = error "Invalid threshold. Thresholds must be in [0,1]."
                            | not wellFormedSNM = error $ "Social Networks Model is not well-formed. \n" ++ unlines errorList
                            | otherwise         = updSelecVariant tau snm
        where
            (wellFormedSNM, errorList) = isWellFormedSNModel snm





--------------------------------------------------------------------------------
-- Basic social influence update
--------------------------------------------------------------------------------


{-
Input:
tau: Threshold
m: SNModel

! Assumes m is a well-formed Social Networks model and tau is in [0,1].

Output:
Performs the Basic social influence update on m with the provided threshold tau.

General properties:
 - not idempotent
 - not accumulative

Explanation:

update_per_topic:
The social influence update changes the dual valuation of each topic independently.
We therefore take care of each topic one after another.


(T 0):
(T 0) is reserved for internal use. If (T 0) is a topic in the input,
this signals that updInflBasic was called form within updInflVariant.
updInflVariant combines the relations for each topic into one. After this,
the variant social influence update works like the basic one, and
we can use the updInflBasic function.


The new positions an agent takes solely depend on the positions of their friends.
This means, any two agents who share the identical set of friends, will end up with the same adopted positions.
Therefore, we can compute the new positions once for each set of friends (=friendsgroup) that is present:

buildFriendsGroupMap :: [AgentSet] -> M.Map AgentSet (Set Position)
Takes a duplicate-free list of sets of Agents (friendgroups) and computes the set of positions that
an agents with this set of friends will hold after the update. Returns a map.

friendsGroupMap :: M.Map AgentSet (Set Position)
Maps sets of friends to sets of positions. Indicates that an agent with this set of friends
will adopt this set of positions after the update.

getNewPos :: Agent -> Set Position
Returns the set of positions the agents adopts after the update.

-}
updInflBasic :: Double -> SNModel ->SNModel
updInflBasic tau m@(SNM nrAgents' positions' rel' dualVal') = m { dualVal = M.mapWithKey update_per_topic dualVal' } where
    combinedFriendsGroups | T 0 `M.member` rel' = L.nub $ V.toList (rel' ! T 0) --In Variant case: Saves computing the nub several times.
                          | otherwise = []
    --Agents that don't adopt any positions in the topic are ommitted from the map.
    update_per_topic t dualVal_t = IntMap.fromList $ filter (not . null . snd) $ map (\i -> (i, getNewPos i)) [0..(nrAgents'-1)]
        where
        friendsGroupMap | tau==0    = M.empty --If tau is zero, we don't need this computation.
                        | T 0 `M.member` rel' = buildFriendsGroupMap combinedFriendsGroups
                        | otherwise = buildFriendsGroupMap $ L.nub $ V.toList (rel' ! t)

        buildFriendsGroupMap [] = M.empty
        buildFriendsGroupMap (x:xs) = M.insert x (computePosSet tau (IntSet.size x) posList) restMap
                                        where
                                        restMap = buildFriendsGroupMap xs
                                        --posList concatenates all positions that the agents in x take (including duplicates).
                                        posList = concatMap (S.toList . flip lookupDualVal dualVal_t) (IntSet.toList x)

        getNewPos ag | nr_friends == 0                 = lookupDualVal ag dualVal_t  --if ag has no friends, positions stay the same
                     | tau == 0                        = positions' ! t              --if tau is zero, all people with friends get the full positions list of the topic
                     | otherwise                       = friendsGroupMap ! friends   --assign the updated positions for agents with this set of friends
                     where
                            friends | T 0 `M.member` rel' = (rel'! T 0) V.! ag
                                    | otherwise = (rel' ! t) V.! ag
                            nr_friends = IntSet.size friends



{-
Input:
tau:        threshold
nr_friends: size of friendgroup
posList:    positions of all friends (including duplicates)

Output:
Returns the set of positions that an agent will adopt who has a friendgroup of size nr_friends,
and whose friends take the positions in posList.
-}
computePosSet :: Ord a => Double -> Int -> [a] -> Set a
computePosSet tau nr_friends posList = S.fromList . map fst . filter friendsThink $ M.toList $ countOccur posList where
    friendsThink (_, occur) = fromIntegral occur / fromIntegral nr_friends >= tau



--------------------------------------------------------------------------------
-- Basic friendship selection update
--------------------------------------------------------------------------------


{-
Input:
tau: Threshold
m: SNModel

! Assumes m is a well-formed Social Networks model and tau is in [0,1].

Output:
Performs the Basic friendship selection update on m with the provided threshold tau.


General properties:
 - Produces reflexive and symmetric relations.
 - Indempotent with constant tau
 - Not accumulative
 - Application of two basic friendship selection updates with different tau makes the first applied irrelevant.


Explanation:

update_per_topic:
The friendship selection update changes the relation of each topic independently.
We therefore take care of each topic one after another.

getNewFriends:
Returns the set of friends of an agent after the update.
This is done by converting the intermediate adjacency matrix into the Vector AgentSet representation.

this_Ts_Rel_Matrix:
An intermediate adjacency matrix that is built for the relation after the update.

addifTrue:
Helps converting a row of the intermediate adjacency matrix into the AgentSet representation.
-}
updSelecBasic::  Double -> SNModel -> SNModel
--Edge Case: For tau = 0, all nodes become friends with all other nodes.
updSelecBasic 0 m = makeFullRelModel m
updSelecBasic tau m@(SNM nrAgents' positions' oldrel dualVal') = m {rel = M.mapWithKey update_per_topic oldrel } where
        update_per_topic t = V.imap getNewFriends where
            getNewFriends ag _ = V.ifoldl' addifTrue IntSet.empty $ Mat.getRow (ag+1) this_Ts_Rel_Matrix
            this_Ts_Rel_Matrix = buildRelMatrix nrAgents' (dualVal' ! t) (S.size (positions' ! t )) tau
            addifTrue curSet idx ele | ele = IntSet.insert idx curSet
                                     | otherwise = curSet


{-
Input:
nrAgs:     number of Agents
dualVal_t: dual valuation for one topic
p:         number of positions for topic t
tau:       threshold

Output:
Computes an intermediate adjacency matrix for the relation for topic t after the update.

Explanation:
As the update produces reflexive and symmetric relations, we only compute the lower triangle.
The diagonal contains only True (reflexive), and the upper triangle can be filled using makeSymMat.

Sidenote: Matrices are indexed starting from 1, whereas Vectors as indexed starting from 0.

pred_sim_t (i, j) computes a single entry of the intermediate adjacency matrix.
If it returns True, this means: agents i-1 and agents j-1 are friends after the update.
-}
buildRelMatrix :: Int -> IntMap (Set Position) -> Int -> Double -> Matrix Bool
buildRelMatrix nrAgs dualVal_t p tau = makeSymMat $ Mat.matrix nrAgs nrAgs pred_sim_T where
    --Precompute the number of positions each agent takes. Avoids repeated computation.
    posSizesVector = precomputeSetSize nrAgs dualVal_t
    pred_sim_T (i, j)  | i<=j      = True --We only compute the lower triangle.
                       | otherwise = fromIntegral (bothHave + bothNotHave) / fromIntegral p >= tau where
                                        bothHave = S.size $ S.intersection i_pos j_pos     --Number of positions of topic t that both agents have adopted.
                                        bothNotHave = p - (nr_i_pos + nr_j_pos - bothHave) --Number of positions of topic t that both agents have not adopted.
                                        i_pos = lookupDualVal (i-1) dualVal_t --Positions agent i-1 takes.
                                        j_pos = lookupDualVal (j-1) dualVal_t --Positions agent j-1 takes.
                                        nr_i_pos = posSizesVector V.! (i-1)   --Number of positions agent i-1 takes.
                                        nr_j_pos = posSizesVector V.! (j-1)   --Number of positions agent j-1 takes.





--------------------------------------------------------------------------------
-- Extended social influence update
--------------------------------------------------------------------------------

{-
Input:
tau: Threshold
m: SNModel

! Assumes m is a well-formed Social Networks model and tau is in [0,1].

Output:
Performs the extended social influence update on m with the provided threshold tau.

Explanation:
The extended social influence update take into account the positions of all friends (no matter the topic).
Therefore, the update calls updInflBasic with a SNM that is the same except it only has one combined relation
for a topic (T 0). This topic is reseved for this special case.
-}
updInflVariant :: Double -> SNModel -> SNModel
updInflVariant tau (SNM nragents' positions' rel' dualVal') =  SNM nragents' positions' rel' newDualVal where
    newDualVal = dualVal (updInflBasic tau (SNM nragents' positions' rel'' dualVal'))
    rel'' = M.singleton (T 0) (combinedTopicsRel nragents' rel')


--------------------------------------------------------------------------------
-- Restricted friendship selection update
--------------------------------------------------------------------------------

{-
Input:
tau: Threshold
m: SNModel

! Assumes m is a well-formed Social Networks model and tau is in [0,1].

Output:
Performs the restricted friendship selection update on m with the provided threshold tau.


Properties:
Only agents that are socially reachable for an agent i
(i.e. in the reflexive and transitive closure of the union of relations over all topics)
can become friends with agent i.


Explanation:

transClosure:
Computes the reflexive and transitive closure of the union of the relations of all topics.

thisTsRel t:
Computes the new relation for topic t. Proceeds by computung the new friends for each agent (newFriends ag).

newFriends ag:
Computes the new set of frineds of agent ag for the current topic.
Proceeds by filtering the set of potential friends (all socially reachable).

pred_sim_T i j:
Predicate indicating if agent i and agent j will be friends on topic T after the update.
-}
updSelecVariant :: Double -> SNModel -> SNModel
updSelecVariant tau m@(SNM nrAgents' positions' rel' dualVal') = m {rel = newRel} where
    newRel = M.fromList [(t, thisTsRel t)| t <- M.keys positions']
    transClosure = makeReflexive $ makeTransitive $ combinedTopicsRel nrAgents' rel'
    thisTsRel t = V.fromList [newFriends ag| ag <- [0..nrAgents'-1] ] where
        dualVal_t = dualVal' ! t   --Dual valuation for topic t.
        p = S.size $ positions'! t -- Number of positions in topic t.
        posSizesVector = precomputeSetSize nrAgents' dualVal_t --Number of positions each agents has adopted in topic t.
        newFriends ag = IntSet.filter (pred_sim_T ag) potentialFriends where
            potentialFriends = transClosure V.! ag
        pred_sim_T i j = fromIntegral (bothHave + bothNotHave) / fromIntegral p >= tau where
                                        bothHave = S.size $ S.intersection i_pos j_pos     --Number of positions of topic t that both agents have adopted.
                                        bothNotHave = p - (nr_i_pos + nr_j_pos - bothHave) --Number of positions of topic t that both agents have not adopted.
                                        i_pos = lookupDualVal i dualVal_t --Positions agent i takes.
                                        j_pos = lookupDualVal j dualVal_t --Positions agent j takes.
                                        nr_i_pos = posSizesVector V.! i   --Number of positions agent i takes.
                                        nr_j_pos = posSizesVector V.! j   --Number of positions agent j takes.


--------------------------------------------------------------------------------
-- Interleaving of updates
--------------------------------------------------------------------------------

{-
Input:
Mode of Selec
Mode of Infl
tau: Threshold
snm: SNModel

Output:
Checks whether tau is in [0,1] and whether snm is well-formed.
If both conditions hold, calls the function interleave.
-}
validInterleave :: Mode -> Mode -> Double -> SNModel -> (SNModel, Maybe Int)
validInterleave modeS modeI tau snm  | not $ validTau tau = error "Invalid threshold. Threshold must be in [0,1]."
                                    | not wellFormedSNM  = error $ "Social Networks Model is not well-formed. \n" ++ unlines errorList
                                    | otherwise = interleave modeS modeI tau snm
                    where
                        (wellFormedSNM, errorList) = isWellFormedSNModel snm




{-
Input:
Mode of Selec
Mode of Infl
Threshold
SNM

! Assumes valid threshold and well-formed SNModel.


Output:
Applies an interleaving of social influence and friendship selection with given threshold to the SNM
until stabilization is reached.
Returns a tuple of (resulting model after stabilization, number of iterations performed).

If no stabilization was reached after 20 steps, the execution is stopped and Nothing is returned
instead of the number.
-}
interleave :: Mode -> Mode -> Double -> SNModel -> (SNModel, Maybe Int)
interleave Basic Basic tau     | not $ validTau tau = error "Invalid threshold. Threshold must be in [0,1]."
                               | otherwise          = stabCountSafe 20 (updSelecBasic tau . updInflBasic tau)
interleave Basic Variant tau   | not $ validTau tau = error "Invalid threshold. Threshold must be in [0,1]."
                               | otherwise          = stabCountSafe 20 (updSelecBasic tau . updInflVariant tau)
interleave Variant Basic  tau  | not $ validTau tau = error "Invalid threshold. Threshold must be in [0,1]."
                               | otherwise          = stabCountSafe 20 (updSelecVariant tau . updInflBasic tau)
interleave Variant Variant tau | not $ validTau tau = error "Invalid threshold. Threshold must be in [0,1]."
                               | otherwise          = stabCountSafe 20 (updSelecVariant tau . updInflVariant tau)




--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

{-
Takes a list and returns a frequency map indicating the number of times an element occurred in the input.
-}
countOccur :: Ord a => [a] -> M.Map a Int
countOccur = L.foldl' (\cur a -> M.insertWith (+) a 1 cur) M.empty


{-
Safe lookup for non-total dual valuation map.
If an Agent is not the map, their set of positions is empty.
-}
lookupDualVal :: IntMap.Key -> IntMap (Set a) -> Set a
lookupDualVal = IntMap.findWithDefault S.empty



{-
Computes the sizes of the sets in a IntMap. Stores in a vector for O(1) access.
At index i the vector stores the size of the set mapped from the key i.
If a key is not in the map, stores 0.
Checks keys up to nrAgs.

Example: Takes dualVal_t and gives the number of positions held by each agent on topic t.
-}
precomputeSetSize :: Int -> IntMap (Set b) -> Vector Int
precomputeSetSize nrAgs dualVal_t = V.generate nrAgs (\i -> S.size (lookupDualVal i dualVal_t))



{-
Takes a lower triangular matrix and returns the symmetric matrix obtained by mirroring
the lower triangle to the upper triangle.

Example:

    Input:                 Output:

    [ a  .  .  . ]         [ a  b  c  d ]
    [ b  e  .  . ]         [ b  e  f  g ]
    [ c  f  h  . ]   -->   [ c  f  h  i ]
    [ d  g  i  j ]         [ d  g  i  j ]
-}
makeSymMat :: Matrix a -> Matrix a
makeSymMat m = Mat.mapPos sym m where
    sym (i, j) e | i>=j = e
                 | otherwise = m Mat.! (j,i)



{-
Forms the union of relations over all topics.
-}
combinedTopicsRel :: Int -> M.Map Topic Relation -> Relation
combinedTopicsRel nragents' = M.foldl' combineRelation (V.replicate nragents' IntSet.empty)


{-
Input:
maxIter: maximum number of iterations
f: function (endomorphism)

Output:
Returns the function that will apply f until the output is stable or the maximum number of iterations has been reached.
Then it will return a tuple of (stabilized output, number of iterations it took until stable).
If stabilization wasn't reached in maxIter rounds, Nothing is returned for the number of iterations.
-}
stabCountSafe :: Eq a => Int -> (a -> a) -> a -> (a, Maybe Int)
stabCountSafe maxIter f = go 0 where
    go k current | k >= maxIter  = (current, Nothing)
                 | x' == current = (current, Just k)
                 | otherwise     = go (k + 1) x'
      where
        x' = f current