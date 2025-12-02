module Semantics where


--TODO only necessary imports
import Syntax ( Form(..))
import SNModel ( SNModel(rel, dual, SNM), Position, makeFullRelModel)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import SetTheory (makeTransitive, makeReflexive, makeSymmetric)
import qualified Data.Matrix as Mat
import Data.Matrix (Matrix)
import qualified Data.Vector as V
import Data.Vector (Vector)
import qualified Data.List as L (group, sort, nub)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.Maybe ( isJust, fromJust )

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

(|=) m (Infl tau f)                             = (|=) (updInflPreComp tau m) f
(|=) m (Selec tau f)                            = (|=) (updSelecMatrix tau m) f


{-
Performs the social influence operation on the model with the provided threshold.
Assumes tau is in [0,1].

Properties:
 - NOT idempotent
 - in general it does not depend on the current positions (eg. it's not accumulative)
-}


--Assumes we have agents 1...n
updInflPreComp :: Double -> SNModel ->SNModel
updInflPreComp tau m@(SNM _ positions' rel' dual') = m { dual = M.mapWithKey update_per_topic dual' } where
    update_per_topic t dual_t = IntMap.mapWithKey getNewPos dual_t where --TODO only works for full maps
        friendsGroupMap | tau==0    = M.empty --if tau is zero, we don't have to compute anything
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
                       | tau == 0                        = positions' ! t
                       | otherwise                       = S.fromList . map fst . filter friendsThink $ friendsGroupMap ! friends  where --should always be present, otherwise it's a mistake
                            friends = (rel' ! t) IntMap.! ag
                            nr_friends = IntSet.size $ friends
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

{-

Performs the friendship selection operation on the model with the provided threshold.
Assumes tau is in [0,1]

Properties:
 - produces reflexive and symmetric relations
 - idempotent with constant tau
 - application of two selec operation with different tau makes the first irrelevant
 - in general does not depend on current relation
-}


--assume agents are contiguous from 1...n

buildRelMatrix :: IntMap (Set Position) -> Int -> Double -> Matrix Bool
buildRelMatrix dual_t p tau = makeSymMat $ Mat.matrix nrAgs nrAgs pred_sim_T where
    nrAgs = IntMap.size dual_t
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



--performs Update Selec tau
--translates the computed symmetric adjacency matrix into the adjacency set representation
updSelecMatrix::  Double -> SNModel -> SNModel
updSelecMatrix 0 m = makeFullRelModel m
updSelecMatrix tau m@(SNM _ positions' oldrel dual') = m {rel = M.mapWithKey update_per_topic oldrel } where
        update_per_topic t = IntMap.mapWithKey getNewFriends where
            this_Ts_Rel_Matrix = buildRelMatrix (dual' ! t) (S.size (positions'! t )) tau
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





{-
usage in ghci
examleSmall |=
-}

