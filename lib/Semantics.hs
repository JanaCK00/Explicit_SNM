module Semantics where


--TODO only necessary imports
import Syntax ( Form(..), Prp(Connected, Adopted), UpOperator (Infl, Selec) )
import SNModel ( SNModel(rel, dual, SNM), Position)
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
import qualified Data.List as L (group, sort)
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap

{-
Semantics defined on Formulas as defined in Syntax.
Update functions for Selec and Infl.

(The default should be, that these are working with simplified formulas already,
in order to avoid irrelevant and costly update operations.)
-}

(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (PrpF (Adopted agent position'))         = any ((position' `S.member`) . flip (IntMap.!) agent) (dual m) --TODO with dual this is slower sadly :( bc. we have to search each topic for the position in question, (and bc positions aren't intsets, but we assume more agents and searching the map also takes log n). wonder if the easier update makes up for it...but I do think so
(|=) m (PrpF (Connected topic agent1 agent2))   = agent2 `IntSet.member`((rel m ! topic) IntMap.! agent1)
(|=) m (Neg f)                                  = not $ m |= f
(|=) m (Conj fs)                                = all (m |=) fs --returns true on empty list
(|=) m (Disj fs)                                = any (m |=) fs --returns false on an empty list
(|=) m (Impl f g)                               = not (m |= f) || m |= g

(|=) m (Update (Infl tau) f)                    = (|=) (updInflPreComp tau m) f
(|=) m (Update (Selec tau) f)                   = (|=) (updSelecMatrix tau m) f


{-
Performs the social influence operation on the model with the provided threshold.
Assumes tau is in [0,1].

Properties:
 - NOT idempotent
 - in general it does not depend on the current positions (eg. it's not accumulative)
-}

--Assumes we have agents 1...n
--also here: can we just store it in a matrix? bc I have to go though everything anyway and that way also access would be O(1)
updInflPreComp :: Double -> SNModel ->SNModel
updInflPreComp tau m@(SNM _ positions' rel' dual') = m { dual = M.mapWithKey update_per_topic dual' } where
    update_per_topic t dual_t = IntMap.mapWithKey getNewPos dual_t where
        this_Ts_N_size_vector = precomputeIntSetSize (rel' ! t)
        getNewPos ag _ | nr_friends == 0                 = dual_t IntMap.! ag --if no friends, positions stay the same
                       | tau == 0                        = positions' ! t--TODO change if i delete the positions map from the SNModel representation
                       | otherwise                       = S.fromList . map fst . filter friendsThink $ countOccur (concatMap (S.toList . (dual_t IntMap.!)) (IntSet.toList friends)) where --IDEA could I maybe make a note that I have this already and reuse it? even parts, where friends are subsets...
                            friends = (rel' ! t) IntMap.! ag
                            friendsThink (_, occur) = fromIntegral occur / fromIntegral nr_friends >= tau
                            nr_friends = this_Ts_N_size_vector V.! (ag-1)



--takes a list and return a list of tuples indicating the number of times an element occured in the input
countOccur :: Ord a => [a] -> [(a, Int)]
countOccur xs = [(head g, length g) | g <- L.group (L.sort xs)] --return empty list for empty list input


{-
Precompute (??TODO does that really happen) the sizes of the sets in a map. Stores in a vector for O(1) access
--takes dual_t for updSelec and gives the nr of pos held per agent
--takes rel_t for updInfl and gives the nr of friends per agent
-}
precomputeSetSize :: IntMap (Set b) -> Vector Int
precomputeSetSize = V.fromList . map S.size . IntMap.elems

precomputeIntSetSize :: IntMap IntSet -> Vector Int
precomputeIntSetSize = V.fromList . map IntSet.size . IntMap.elems



{-

Performs the friendship selection operation on the model with the provided threshold.
Assumes tau is in [0,1]

Properties:
 - produces reflexive and symmetric relations
 - idempotent with constant tau
 - application of two selec operation with different tau makes the first irrelevant
 - in general does not depend on current relation
-}


--TODO working on this, want a matrix that relates agents based on current val
    --would it be nice to always have such an indexable matrix for the relations?  If I have to create it anyway each time I use a Selec?

--assume agents are contiguous from 1...n
--WAIT do I even need the slicing access? can't I just have a list of lists and then map over it to construct the sets?
--Whats better: constructing them only partially and later making it symmetric. Or mirroring this matrix?

buildRelMatrix :: IntMap (Set Position) -> Int -> Double -> Matrix Bool
buildRelMatrix dual_t p tau = makeSymMat $ Mat.matrix nrAgs nrAgs pred_sim_T where
    nrAgs = IntMap.size dual_t
    pred_sim_T (i, j)  | i<=j      = True
                       | otherwise = fromIntegral (p - (nr_i_pos + nr_j_pos) + 2 * nr_intersect) / fromIntegral p >= tau where
                                        nr_intersect = S.size $ S.intersection i_pos j_pos
                                        i_pos = dual_t IntMap.! i --TODO avoid accessing this too many times? But I think avoiding the upper triangle is already all I can do
                                        j_pos = dual_t IntMap.! j
                                        nr_i_pos = posSizesVector V.! (i-1)
                                        nr_j_pos = posSizesVector V.! (j-1)
                                        posSizesVector = precomputeSetSize dual_t

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





--TODO ?  keep working on this
--maybe I can make it from a list ? where I prepend stuff, so I only go through the sizes less? Or shoudl I precompute the sizes as well?
{-
newtype SymMatrix a = SM {v :: V.Vector } --a symmetric matrix, stored as a vector of the lower triangle
    deriving (Eq, Ord, Show)

symMatsize :: SymMatrix a -> Int
symMatsize (SM v) = --TODO

row :: Int -> V.Vector oder so

-}

--IDEA: what about a map from tuples of position combos to the size_sim_T? so that won't have to be computed everytime?


--takes a SNModel and makes full relations for all topics
makeFullRelModel :: SNModel -> SNModel
makeFullRelModel m@(SNM nrAgents' _ rel' _) = m { rel = M.map fullRel rel' } where
    fullRel = IntMap.map allFriends
    allFriends _ = IntSet.fromList [1..nrAgents']

--takes a SNModel and makes all its relations reflexive
makeReflModel :: SNModel -> SNModel
makeReflModel m@(SNM _ _ rel' _) = m {rel = M.map makeReflexive rel'}

--takes a SNmodel and makes all its relations symmetric
makeSymModel :: SNModel -> SNModel
makeSymModel m@(SNM _ _ rel' _) = m {rel = M.map makeSymmetric rel'}

--takes a SNModel and makes all its relations transitive
makeTransModel :: SNModel -> SNModel
makeTransModel m@(SNM _ _ rel' _) = m {rel = M.map makeTransitive rel'}


{-
usage in ghci
examleSmall |=
-}

