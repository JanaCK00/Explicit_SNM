module Semantics where


--TODO only necessary imports
import Syntax ( Form(..), Mode(..))
import SNModel ( SNModel(rel, dual, SNM), Position, makeFullRelModel, Topic(..))
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import qualified Data.Matrix as Mat
import Data.Matrix (Matrix)
import qualified Data.Vector as V
import Data.Vector (Vector)
import qualified Data.List as L (group, sort, nub)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.List as L
import SetTheory (Relation, makeTransitive, makeReflexive)

{-
Semantics defined on Formulas as defined in Syntax.
Update functions for Selec and Infl.

(The default should be, that these are working with simplified formulas already,
in order to avoid irrelevant and costly update operations.)
-}

(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (Adopted agent position')                = any ((position' `S.member`) . flip (IntMap.!) agent) (dual m) --TODO with dual this is slower sadly :( bc. we have to search each topic for the position in question, (and bc positions aren't intsets, but we assume more agents and searching the map also takes log n). wonder if the easier update makes up for it...but I do think so
(|=) m (Connected topic agent1 agent2)          = agent2 `IntSet.member`((rel m ! topic) IntMap.! agent1)
(|=) m (Neg f)                                  = not $ m |= f
(|=) m (Conj fs)                                = all (m |=) fs --returns true on empty list
(|=) m (Disj fs)                                = any (m |=) fs --returns false on an empty list
(|=) m (Impl f g)                               = not (m |= f) || m |= g

(|=) m (Infl Basic tau f)                       = (|=) (updInflBasic tau m) f --Basic: Social Influence
(|=) m (Selec Basic tau f)                      = (|=) (updSelecBasic tau m) f --Basic: Friendship Selection

(|=) m (Infl Variant tau f)                     = (|=) (updInflVariant tau m) f --Variant: Extended Social Influence
(|=) m (Selec Variant tau f)                    = (|=) (updSelecVariant tau m) f --Variant: Restrited Friendship Selection




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
Performs the Basic social influence operation on the model with the provided threshold.
Assumes tau is in [0,1].

Properties:
 - NOT idempotent
 - in general it does not depend on the current positions (eg. it's not accumulative)
 - Infl 1 -> drop all positions except if all neighbors agree on it, or neighboorhood is empty
 - Infl 0 -> pick up all positions, except if neighboorhood is empty
-}

updInflBasic :: Double -> SNModel ->SNModel
updInflBasic tau m@(SNM _ positions' rel' dual') = m { dual = M.mapWithKey update_per_topic dual' } where
    update_per_topic t dual_t = IntMap.mapWithKey getNewPos dual_t where --TODO only works for full maps
        friendsGroupMap | tau==0    = M.empty --if tau is zero, we don't have to compute anything
                        | (T 0) `M.member` rel' = buildFriendsGroupMap $ L.nub $ IntMap.elems (rel' ! (T 0)) --TODO this is definitely not good, it does it everytime!
                        | otherwise = buildFriendsGroupMap $ L.nub $ IntMap.elems (rel' ! t)
        --buildFriendsGroupMap :: [IntSet] -> M.Map Set [(Position, Int)]
        --it takes a duplicate-free list of Sets of Agents (friendgroups) and combines and counts the positions they hold
        --this allows to avoid computing the count several times on cases of identical friendgroups
        --makes it slower (additional lookup) if we have all different friend groups. but that isn't very likely and I think we save some time when there are many people with the same friend group
        --TODO if stuff was ordered, we could consider searching for subsets in the map... not sure how much sense that would make though
        buildFriendsGroupMap [] = M.empty
        buildFriendsGroupMap (x:xs) = M.insert x (countOccur  (concatMap (S.toList . (dual_t IntMap.!)) (IntSet.toList x))) restMap  where
                                        restMap = buildFriendsGroupMap xs
        getNewPos ag _ | nr_friends == 0                 = dual_t IntMap.! ag --if ag has no friends, positions stay the same
                       | tau == 0                        = positions' ! t --if tau is zero, all people with friends get the full positions list of the topic
                       | otherwise                       = S.fromList . map fst . filter friendsThink $ friendsGroupMap ! friends  where --should always be present, otherwise it's a mistake
                            friends | (T 0) `M.member` rel' = (rel'! (T 0)) IntMap.! ag --case for Variant Infl
                                    | otherwise = (rel' ! t) IntMap.! ag
                            nr_friends = IntSet.size friends
                            friendsThink (_, occur) = fromIntegral occur / fromIntegral nr_friends >= tau


--takes a list and return a list of tuples indicating the number of times an element occured in the input
countOccur :: Ord a => [a] -> [(a, Int)]
countOccur xs = [(head g, length g) | g <- L.group (L.sort xs)] --return empty list for empty list input



{-
Precompute  the sizes of the sets in a map. Stores in a vector for O(1) access
--takes dual_t for updSelec and gives the nr of pos held per agent
-}
precomputeSetSize :: IntMap (Set b) -> Vector Int
precomputeSetSize = V.fromList . map S.size . IntMap.elems



--assume agents are contiguous from 1...n

buildRelMatrix :: Int -> IntMap (Set Position) -> Int -> Double -> Matrix Bool
buildRelMatrix nrAgs dual_t p tau = makeSymMat $ Mat.matrix nrAgs nrAgs pred_sim_T where
    posSizesVector = precomputeSetSize dual_t
    pred_sim_T (i, j)  | i<=j      = True
                       | otherwise = fromIntegral (p - (nr_i_pos + nr_j_pos) + 2 * nr_intersect) / fromIntegral p >= tau where
                                        nr_intersect = S.size $ S.intersection i_pos j_pos
                                        i_pos = dual_t IntMap.! i
                                        j_pos = dual_t IntMap.! j
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
updSelecBasic::  Double -> SNModel -> SNModel
updSelecBasic 0 m = makeFullRelModel m
updSelecBasic tau m@(SNM nrAgents' positions' oldrel dual') = m {rel = M.mapWithKey update_per_topic oldrel } where
        update_per_topic t = IntMap.mapWithKey getNewFriends where
            this_Ts_Rel_Matrix = buildRelMatrix nrAgents' (dual' ! t) (S.size (positions'! t )) tau
            getNewFriends ag _ = V.ifoldl' addifTrue IntSet.empty $ Mat.getRow ag this_Ts_Rel_Matrix
            addifTrue curSet idx ele | ele = IntSet.insert (idx+1) curSet
                                     | otherwise = curSet


--TODO ?  keep working on this; construction of vector
--maybe I can make it from a list ? where I prepend stuff, so I only go through the sizes less? Or shoudl I precompute the sizes as well?
--ACHTUNG vector is 1 based!!
newtype SymMatrix = SM {v :: V.Vector Bool } --a symmetric matrix, stored as a vector of the lower triangle. (without diagonal, bc. it always holds True)
    deriving (Eq, Ord, Show)


--one based access to symmetric matrix with True on the diagonal
access :: SymMatrix -> (Int,Int) -> Bool
access (SM v') (i,j) | i==j      = True
                     | i < j     = access (SM v') (j,i)
                     | otherwise = v' V.! (sumUp (i-2) + j) where
                        sumUp n = (n*(n+1)) `div` 2


--have something to traverse a row




--TODO CHECK if this works
--combines the topic-specific relations to one relation
combinedTopicsRel :: M.Map Topic Relation -> Relation
combinedTopicsRel = M.foldl' (IntMap.unionWith IntSet.union) IntMap.empty

--TODO CONTINUE HERE complete these, THINK ABOUT updInflBasic if it works for this case and if it doesn't look stuff up too many times!!!
    --I might keep this version around for comparison
updInflVariant :: Double -> SNModel -> SNModel
updInflVariant tau (SNM agents' positions' rel' dual') =  SNM agents' positions' rel' newDual where
    newDual = dual (updInflBasic tau (SNM agents' positions' rel'' dual'))
    rel'' = M.singleton (T 0) (combinedTopicsRel rel')

updSelecVariant :: Double -> SNModel -> SNModel
updSelecVariant tau m@(SNM nrAgents' positions' rel' dual') = m {rel = newRel} where
    newRel = M.fromList [(t, thisTsRel t)| t <- M.keys positions']
    transClosure = makeReflexive $ makeTransitive $ combinedTopicsRel rel'
    thisTsRel t = IntMap.fromList [(ag, newFriends ag)| ag <- [1..nrAgents'] ] where
        dual_t = dual' ! t
        p = S.size $ positions'! t
        posSizesVector = precomputeSetSize dual_t
        newFriends ag = IntSet.filter (pred_sim_T ag) (transClosure IntMap.! ag) --TODO looking this up too many times?
        pred_sim_T i j = fromIntegral (p - (nr_i_pos + nr_j_pos) + 2 * nr_intersect) / fromIntegral p >= tau where
                                        nr_intersect = S.size $ S.intersection i_pos j_pos
                                        i_pos = dual_t IntMap.! i
                                        j_pos = dual_t IntMap.! j
                                        nr_i_pos = posSizesVector V.! (i-1)
                                        nr_j_pos = posSizesVector V.! (j-1)
--use makeTransitive on the combined relations from SetTheory to get the Set of possible agents


{-
usage in ghci
examleSmall |=
-}

