module Semantics where


--TODO only necessary imports
import Syntax ( Form(..), Mode(..), isInUpdateModeCons, simplify, getAgs, getTops, getPos)
import SNModel ( SNModel(rel, dualVal, SNM, nrAgents, positions), Position, makeFullRelModel, Topic(..), isValidSNModel, Relation, makeTransitive, makeReflexive, combineRelation)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import qualified Data.IntSet as IntSet
import qualified Data.Matrix as Mat
import Data.Matrix (Matrix)
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as L


{-
TODO test
Safe model checker function

Input:
SNModel snm
Form f

Output:
Checks if the Form is in-update mode consistent. --TODO maybe change to mode-consistent
Checks if the SNModel is valid.
Checks if agents, topics and positions appearing in Form also appear in SNModel

If all conditions hold, simplifies f and checks if f holds on snm.
-}
(*|=) :: SNModel -> Form -> Bool
(*|=) snm f | not (isInUpdateModeCons f) = error "Formula is not at least in-operator mode-consistent." --TODO maybe change to mode-consistent?
            | not (isValidSNModel snm)    = error "Social Networks Model is not valid."
            | not (match snm f)           = error "Formula contains Agents, Topics or Positions that aren't present in the Social Networks Model."
            | otherwise                   = snm |= simplify f


match :: SNModel -> Form -> Bool
match snm f = matchAg && matchTop && matchPos where
    matchAg = maximum (IntSet.toList $ getAgs f) <= nrAgents snm
    matchTop = getTops f `S.isSubsetOf` M.keysSet (positions snm)
    matchPos = getPos f `S.isSubsetOf` M.foldr S.union S.empty (positions snm)


{-
Semantics defined on Formulas as defined in Syntax.
Update functions for Selec and Infl.

(The default should be, that these are working with simplified formulas already,
in order to avoid irrelevant and costly update operations.)
-}
--assumes that the form only contains propositions that match the model (so agents / positions / topics that are part of the model)

(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (Adopted agent position')                = any ((position' `S.member`) . lookupDualVal agent) (dualVal m) -- faster now that we don't have full maps in dualVal. with dualVal this is slower sadly :( bc. we have to search each topic for the position in question, (and bc positions aren't intsets, but we assume more agents and searching the map also takes log n). wonder if the easier update makes up for it...but I do think so
(|=) m (Connected topic agent1 agent2)          = agent2 `IntSet.member`((rel m ! topic) V.! agent1)
(|=) m (Neg f)                                  = not $ m |= f
(|=) m (Conj fs)                                = all (m |=) fs --returns true on empty list
(|=) m (Disj fs)                                = any (m |=) fs --returns false on an empty list
(|=) m (Impl f g)                               = not (m |= f) || m |= g

(|=) m (Infl Basic tau f)                       = (|=) (updInflBasic tau m) f --Basic: Social Influence
(|=) m (Selec Basic tau f)                      = (|=) (updSelecBasic tau m) f --Basic: Friendship Selection

(|=) m (Infl Variant tau f)                     = (|=) (updInflVariant tau m) f --Variant: Extended Social Influence
(|=) m (Selec Variant tau f)                    = (|=) (updSelecVariant tau m) f --Variant: Restricted Friendship Selection




--not sure if this is needed
{-
Execute a chain of updates (from left to write) on a model and return the resulting model.
The updates are given in syntax Form. Different tau are allowed, and so are different modes.
Example: [Infl Basic 0.5 Top, Selec Variant 0.5 Top] m = updSelecVariant 0.5 (updInflBasic 0.5 m)
-}
executeUpdates :: [Form] -> SNModel -> SNModel
executeUpdates xs m = L.foldl' (\model f -> f model) m (map synToSem xs) where
    synToSem (Infl Basic tau _) = updInflBasic tau
    synToSem (Selec Basic tau _) = updSelecBasic tau
    synToSem (Infl Variant tau _) = updInflVariant tau
    synToSem (Selec Variant tau _) = updSelecVariant tau
    synToSem _ = id --only here for pattern exhaustion, should never be used



{-
Assumes agents are [0..nrAgents'-1]
Performs the Basic social influence operation on the model with the provided threshold.
Assumes tau is in [0,1].

Properties:
 - NOT idempotent
 - in general it does not depend on the current positions (eg. it's not accumulative)
 - Infl 1 -> drop all positions except if (all neighbors agree on it or neighboorhood is empty)
 - Infl 0 -> pick up all positions, except if neighboorhood is empty
-}

--TODO all the T 0 in here are only for the variant infl!

updInflBasic :: Double -> SNModel ->SNModel
updInflBasic tau m@(SNM nrAgents' positions' rel' dualVal') = m { dualVal = M.mapWithKey update_per_topic dualVal' } where
    combinedFriendsGroups | (T 0) `M.member` rel' = L.nub $ V.toList (rel' ! (T 0)) --only for variant infl
                          | otherwise = []
    update_per_topic t dualVal_t = IntMap.fromList $ filter (not . null . snd) $ map (\i -> (i, getNewPos i)) [0..(nrAgents'-1)] where
        friendsGroupMap | tau==0    = M.empty --if tau is zero, we don't have to compute anything
                        | (T 0) `M.member` rel' = buildFriendsGroupMap combinedFriendsGroups --it has to be computed for every topic, BUT the L.nub $ V.toList (rel' ! (T 0)) could be avoided to be computed several times
                        | otherwise = buildFriendsGroupMap $ L.nub $ V.toList (rel' ! t)
        --buildFriendsGroupMap :: [IntSet] -> M.Map Set [(Position, Int)]
        --it takes a duplicate-free list of Sets of Agents (friendgroups) and combines and counts the positions they hold
        --this allows to avoid computing the count several times on cases of identical friendgroups
        --makes it slower (additional lookup) if we have all different friend groups. but that isn't very likely and I think we save some time when there are many people with the same friend group
        --TODO if stuff was ordered, we could consider searching for subsets in the map... not sure how much sense that would make though
        buildFriendsGroupMap [] = M.empty
        buildFriendsGroupMap (x:xs) = M.insert x (computePosSet tau (IntSet.size x) ( concatMap (S.toList . flip lookupDualVal dualVal_t) (IntSet.toList x))) restMap  where
                                        restMap = buildFriendsGroupMap xs
        getNewPos ag | nr_friends == 0                 = lookupDualVal ag dualVal_t  --if ag has no friends, positions stay the same
                     | tau == 0                        = positions' ! t --if tau is zero, all people with friends get the full positions list of the topic
                     | otherwise                       = friendsGroupMap ! friends  where --should always be present, otherwise it's a mistake
                            friends | (T 0) `M.member` rel' = (rel'! (T 0)) V.! ag  --case for Variant Infl
                                    | otherwise = (rel' ! t) V.! ag
                            nr_friends = IntSet.size friends


----takes a list and return a frequency map of indicating the number of times an element occured in the input
countOccur :: Ord a => [a] -> M.Map a Int
countOccur = L.foldl' (\cur a -> M.insertWith (+) a 1 cur) M.empty


--takes tau, size of friendgroup, concatenated positions of all friends (incl dublicates) and returns the new set of positions that an agent will have
--if that was their friendgrup
computePosSet :: Ord a => Double -> Int -> [a] -> Set a
computePosSet tau nr_friends positionsList = S.fromList . map fst . filter friendsThink $ M.toList $ countOccur positionsList where
    friendsThink (_, occur) = fromIntegral occur / fromIntegral nr_friends >= tau

{-
Precompute  the sizes of the sets in a map. Stores in a vector for O(1) access
--takes dualVal_t for updSelec and gives the nr of pos held per agent on that topic
-}
precomputeSetSize :: Int -> IntMap (Set b) -> Vector Int
precomputeSetSize nrAgs dualVal_t = V.generate nrAgs (\i -> S.size (lookupDualVal i dualVal_t))



--assume agents are contiguous from 0...n-1

buildRelMatrix :: Int -> IntMap (Set Position) -> Int -> Double -> Matrix Bool
buildRelMatrix nrAgs dualVal_t p tau = makeSymMat $ Mat.matrix nrAgs nrAgs pred_sim_T where
    posSizesVector = precomputeSetSize nrAgs dualVal_t
    pred_sim_T (i, j)  | i<=j      = True
                       | otherwise = fromIntegral (p - (nr_i_pos + nr_j_pos) + 2 * nr_intersect) / fromIntegral p >= tau where
                                        nr_intersect = S.size $ S.intersection i_pos j_pos
                                        i_pos = lookupDualVal (i-1) dualVal_t
                                        j_pos = lookupDualVal (j-1) dualVal_t
                                        nr_i_pos = posSizesVector V.! (i-1)
                                        nr_j_pos = posSizesVector V.! (j-1)


makeSymMat :: Matrix a -> Matrix a
makeSymMat m = Mat.mapPos sym m where
    sym (i, j) e | i>=j = e
                 | otherwise = m Mat.! (j,i)



{-

Performs the Basic friendship selection operation on the model with the provided threshold.
Assumes tau is in [0,1]

Properties:
 - produces reflexive and symmetric relations
 - idempotent with constant tau
 - application of two selec operation with different tau makes the first irrelevant
 - in general does not depend on current relation
-}
--translates the computed symmetric adjacency matrix into the adjacency set representation
--TODO write a separate translation function for this!

{-
Performs Basic Friendship Selection Update
Input: Threshold, SNM

Edge Case: For Threshold = 0, all nodes become friends with all other nodes.
-}
updSelecBasic::  Double -> SNModel -> SNModel
updSelecBasic 0 m = makeFullRelModel m
updSelecBasic tau m@(SNM nrAgents' positions' oldrel dualVal') = m {rel = M.mapWithKey update_per_topic oldrel } where
        update_per_topic t = V.imap getNewFriends where
            this_Ts_Rel_Matrix = buildRelMatrix nrAgents' (dualVal' ! t) (S.size (positions'! t )) tau
            getNewFriends ag _ = V.ifoldl' addifTrue IntSet.empty $ Mat.getRow (ag+1) this_Ts_Rel_Matrix
            addifTrue curSet idx ele | ele = IntSet.insert idx curSet
                                     | otherwise = curSet


--TODO ?  keep working on this; construction of vector
--maybe I can make it from a list ? where I prepend stuff, so I only go through the sizes less? Or shoudl I precompute the sizes as well?
--ACHTUNG vector is not 1 based!!
newtype SymMatrix = SM {vec :: Vector Bool } --a symmetric matrix, stored as a vector of the lower triangle. (without diagonal, bc. it always holds True)
    deriving (Eq, Ord, Show)


--one based access to symmetric matrix with True on the diagonal
access :: SymMatrix -> (Int,Int) -> Bool
access (SM v') (i,j) | i==j      = True
                     | i < j     = access (SM v') (j,i)
                     | otherwise = v' V.! (sumUp (i-2) + j) where
                        sumUp n = (n*(n+1)) `div` 2


--have something to traverse a row




--combines the topic-specific relations to one relation
combinedTopicsRel :: Int -> M.Map Topic Relation -> Relation
combinedTopicsRel nragents' = M.foldl' combineRelation (V.replicate nragents' IntSet.empty)

    --I might keep this version around for comparison
updInflVariant :: Double -> SNModel -> SNModel
updInflVariant tau (SNM nragents' positions' rel' dualVal') =  SNM nragents' positions' rel' newDualVal where
    newDualVal = dualVal (updInflBasic tau (SNM nragents' positions' rel'' dualVal'))
    rel'' = M.singleton (T 0) (combinedTopicsRel nragents' rel')


updSelecVariant :: Double -> SNModel -> SNModel
updSelecVariant tau m@(SNM nrAgents' positions' rel' dualVal') = m {rel = newRel} where
    newRel = M.fromList [(t, thisTsRel t)| t <- M.keys positions']
    transClosure = makeReflexive $ makeTransitive $ combinedTopicsRel nrAgents' rel'
    thisTsRel t = V.fromList [newFriends ag| ag <- [0..nrAgents'-1] ] where
        dualVal_t = dualVal' ! t
        p = S.size $ positions'! t
        posSizesVector = precomputeSetSize nrAgents' dualVal_t
        newFriends ag = IntSet.filter (pred_sim_T ag) (transClosure V.! ag) --TODO looking this up too many times?
        pred_sim_T i j = fromIntegral (p - (nr_i_pos + nr_j_pos) + 2 * nr_intersect) / fromIntegral p >= tau where
                                        nr_intersect = S.size $ S.intersection i_pos j_pos
                                        i_pos = lookupDualVal i dualVal_t
                                        j_pos = lookupDualVal j dualVal_t
                                        nr_i_pos = posSizesVector V.! i
                                        nr_j_pos = posSizesVector V.! j




--helper function for non-total dualVal
lookupDualVal :: IntMap.Key -> IntMap (Set a) -> Set a
lookupDualVal = IntMap.findWithDefault S.empty

{-
usage in ghci
examleSmall |=
-}

