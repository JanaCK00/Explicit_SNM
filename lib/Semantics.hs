module Semantics where


--TODO only necessary imports
import Syntax ( Form(..), Prp(Connected, Adopted), UpOperator (Infl, Selec) )
import SNModel ( SNModel(rel, val, SNM), Position)
import Data.Map.Strict ((!))
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Set (Set)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import SetTheory (Agent, makeTransitive, makeReflexive, makeSymmetric)
import qualified Data.Matrix as Mat
import Data.Matrix (Matrix)
import qualified Data.Vector as V
import Data.Vector (Vector)
import qualified Data.List as L (group, sort)

{-
Semantics defined on Formulas as defined in Syntax.
Update functions for Selec and Infl.

(The default should be, that these are working with simplified formulas already,
in order to avoid irrelevant update operations.)
-}


(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (PrpF (Adopted agent position'))         = agent `IntSet.member` (val m ! position') --with dual this would need some kind of way to efficiently find the topic of a position...maybe we could put it back in the position, and have a map of the nr pos per topic (instead to the acutal sets), or we could additionally have a map from positions to topics...i don't know
(|=) m (PrpF (Connected topic agent1 agent2))   = agent2 `IntSet.member`((rel m ! topic) ! agent1)
(|=) m (Neg f)                                  = not $ m |= f
(|=) m (Conj fs)                                = all (m |=) fs --returns true on empty list
(|=) m (Disj fs)                                = any (m |=) fs --returns false on an empty list
(|=) m (Impl f g)                               = not (m |= f) || m |= g

(|=) m (Update (Infl tau) f)                    = (|=) (updInfl tau m) f
(|=) m (Update (Selec tau) f)                   = (|=) (updSelec tau m) f


{-
Performs the social influence operation on the model with the provided threshold.
Assumes tau is in [0,1].

Properties:
 - NOT idempotent
 - in general it does not depend on the current positions (eg. it's not accumulative), but after a few steps the changes will probably be smaller?
 --so i might make sense to use map manipulation?? but checking it takes the same time as inserting anway...AND we have the problem of simultanious updates...that could be dangerous
-}

--TODO rewrite but it had worked so far I think
updInfl ::  Double -> SNModel -> SNModel
updInfl tau m@(SNM agents' positions' rel' val') = m { val = newVal } where
    newVal = M.unions [M.fromList [(p, thisPsAgs top p) | p <- S.toList $ positions' ! top] |  top <- M.keys positions']
    thisPsAgs top p = IntSet.filter (friendsThink top p) agents'
    friendsThink top p ag  | IntSet.size (n_T_i top ag) == 0  = ag `IntSet.member` (val' ! p)
                           | otherwise                        = fromIntegral (IntSet.size (IntSet.intersection (n_T_i top ag) (val' ! p) ))/ fromIntegral (IntSet.size (n_T_i top ag)) >= tau
    n_T_i top ag = (rel' ! top) ! ag --TODO is it a problem that this gets looked up many times?


--assume the dual M.Map Topic (M.Map Agent -> (Set Position))
--also here: assume we have agents 1...n
--also here: can we just store it in a matrix? bc I have to go though everything anyway and that way also access would be O(1)

{-updInflPreComp :: Double -> SNModel ->SNModel
updInflPreComp tau m@(SNM agents' positions' rel' dual') = m { dual = M.mapWithKey update_per_topic dual' } where
    update_per_topic t dual_t = M.mapWithKey getNewPos dual_t where
        this_Ts_N_size_vector = precomputeSetSize (rel ! t)
        getNewPos ag ag_pos | nr_friends == 0 = dual_t ! ag --if no friends, positions stay the same
                            | tau == 0                        = positions' ! t--TODO change if i delete the positions map from the SNModel representation
                            | otherwise                       = S.fromList (map fst . filter friendsThink (countOccur (foldl (\cur x -> S.toList (dual_t ! x) ++ cur) [] friends))) where
                                friends = (rel' ! t) ! ag
                                friendsThink (_, occur) = fromIntegral occur / fromIntegral nr_friends >= tau
                                nr_friends = this_Ts_N_size_vector ! ag

-}

--takes a list and return a list of tuples indicating the number of times an element occured in the input
countOccur :: Ord a => [a] -> [(a, Int)]
countOccur xs = [(head g, length g) | g <- L.group (L.sort xs)] --return empty list for empty list input


{-
Precompute the sizes of the sets in a map. Stores in a vector for O(1) access
--alternatively I could just map over it..but that leads to log n access, instead of O(1)
--takes dual_t for updSelec and gives the nr of pos held per agent
--takes rel_t for updInfl and gives the nr of friends per agent
-}
precomputeSetSize :: M.Map a (Set b) -> Vector Int
precomputeSetSize = V.fromList . map S.size . M.elems

{-}
--old ;)
--nehmen wir an wir haben neu ein val wie folgt
--val :: M.Map Topic (M.Map Position AgentSet)

--BE CAREFUL UPDATING THIS BC IT DEPENDS ON EACH OTHER AND SHOULD HAPPEN SIMULTANIOUSLY!! -> use val' for the decision, not whatever intermediate thing is happening
--this is still quadratic in agents, I don't think it's faster at all than the old version
updInflNew ::  Double -> SNModel -> SNModel
updInflNew tau m@(SNM agents' rel' val') = m { val = newVal} where
    newVal = M.mapWithKey myFunction val'
    myFunction t posMap = foldr (subFunction t) posMap agents'
    subFunction t ag curPosMap = M.insertWithKey (checkedInsert t ag) curPosMap
    checkedInsert t ag pos curAgSet | predicate t ag pos = IntSet.insert ag curAgSet --as I go through the tree in both cases anyway, i don't think it's better to manipulate rather than build up??
                                    | otherwise          = IntSet.delete ag curAgSet
    predicate t ag p | IntSet.size (n_T_i t ag) == 0    = ag `IntSet.member` ((val' ! t) ! p)
                     | otherwise                        = fromIntegral (IntSet.size (IntSet.intersection (n_T_i t ag) ((val' ! t) ! p) ))/ fromIntegral (IntSet.size (n_T_i t ag)) >= tau
    n_T_i t ag = (rel' ! t) ! ag --TODO will this be cached?

-}

{-

Performs the friendship selection operation on the model with the provided threshold.
Assumes tau is in [0,1]!

TODO is there another easy edge case? I don't think so...

Properties:
 - produces reflexive and symmetric relations
 - idempotent with constant tau
 - application of two selec operation with different tau makes the first irrelevant
 - in general does not depend on current relation whatsoever, but after a few steps probably the changes will be small, so
 TODO it might make sense to use map manipulation?? but checking takes a long time too...
-}

--TODO rewrite, but this one has worked so far I think
--IDEA look at map manipulations or recursion to try and avoid list comprehension to avoid conversions to maps
--try to think of symmetry, store computation results
updSelec::  Double -> SNModel -> SNModel
updSelec 0 m = makeFullRelModel m
updSelec tau m@(SNM agents' positions' _ val') = m {rel = newRel} where
    newRel = M.fromList [(t, thisTsRel t)| t <- M.keys positions']
    thisTsRel t = M.fromList [(ag, newFriends t ag)| ag <- IntSet.toList agents' ]
    newFriends t ag = IntSet.filter (pred_sim_T t ag) agents'
    pred_sim_T t ag ag2 = fromIntegral (S.size (sim_T t ag ag2)) / fromIntegral (S.size (positions' ! t)) >= tau
    sim_T t ag ag2 = S.filter (agree ag ag2) (positions' ! t)
    agree ag ag2 p = ag `IntSet.member` (val' ! p) && ag2 `IntSet.member` (val' ! p) ||
                           not (ag `IntSet.member` (val' ! p)) && not (ag2 `IntSet.member` (val' ! p))



--assume the dual M.Map Topic (M.Map Agent -> (Set Position))


{-
Sketch without precomputation

updSelec::  Double -> SNModel -> SNModel
updSelec 0 m = makeFullRelModel m
updSelec tau m@(SNM agents' positions' oldrel val') = m {rel = mapWithKey update_per_topic oldrel} where
    update_per_topic t rel_t = mapWithKey get_new_friends rel_t where
        get_new_friends ag friends = foldl' check_and_update friends biggerAgs where
            biggerAgs = S.dropWhileAntitone ((>=) ag) agents' --TODO or just do this using a list?
            check_and_update curGroup ag2 | pred_sim_T ag ag2 = curGroup.insert(ag2)
                                          | otherwise         = curGroup.delete(ag2) --TODO somehow do the symmetric thing too

--this is a relict I think ;) working it into the one above
    thisTsRel t = M.fromList [(ag, newFriends t ag)| ag <- IntSet.toList agents' ]
    newFriends t ag = IntSet.filter (pred_sim_T t ag) agents'
    pred_sim_T t ag ag2 = fromIntegral (sim_T_size t ag ag2) / fromIntegral (nr_pos t) >= tau
    sim_T_size t ag ag2 = (nr_pos t) -() --TODO continue here
    nr_pos t = S.size (positions' ! t)
-}

--TODO working on this, want a matrix that relates agents based on current val
--what if I put the relations like this?? -> not so nice for sparse cases...but I have to go through everyone anyway?
    --would it be nice to always have such an indexable matrix for the relations?  If I have to create it anyway each time I use a Selec?

--TODO : look into matrix (from a generator function), and traversable for later :)
--TODO for now I assume agents are contiguous from 1...n
--WAIT do I even need the slicing access? can't I just have a list of lists and then map over it to construct the sets?
--Whats better: constructing them only partially and later making it symmetric. Or mirroring this matrix?


buildRelMatrix :: M.Map Agent (Set Position) -> Int -> Double -> Matrix Bool
buildRelMatrix dual_t p tau = makeSymMat $ Mat.matrix nrAgs nrAgs pred_sim_T where
    nrAgs = M.size dual_t
    pred_sim_T (i, j)  | i<=j      = True
                       | otherwise = fromIntegral (p - (nr_i_pos + nr_j_pos) + 2 * nr_intersect) / fromIntegral p >= tau where
                                        nr_intersect = S.size $ S.intersection i_pos j_pos
                                        i_pos = dual_t ! i --TODO avoid accessing this too many times? But I think avoiding the upper triangle is already all I can do
                                        j_pos = dual_t ! j
                                        nr_i_pos = posSizesVector V.! i
                                        nr_j_pos = posSizesVector V.! j
                                        posSizesVector = precomputeSetSize dual_t

makeSymMat :: Matrix a -> Matrix a
makeSymMat m = Mat.mapPos sym m where
    sym (i, j) e | i>=j = e
                 | otherwise = m Mat.! (j,i)


{-

--TODO continue here, needs change of SNModel to dual, later think about storing relations as matrices altoghether, then this will also be much easier
--BUT don't delete this translation! for sparse relations the adjacency set is better for traversal (which we need for visualization)
updSelecMatrix::  Double -> SNModel -> SNModel
updSelecMatrix 0 m = makeFullRelModel m
updSelecMatrix tau m@(SNM _ positions' oldrel dual') = m {rel = M.mapWithKey update_per_topic oldrel } where
        update_per_topic t rel_t = M.mapWithKey getNewFriends rel_t where
            this_Ts_Rel_Matrix = buildRelMatrix (dual' ! t) (S.size (positions'! t )) tau --TODO will this be evaluated only once like this?
            getNewFriends ag friends = V.ifoldl' addifTrue IntSet.empty $ Mat.getRow ag this_Ts_Rel_Matrix
            addifTrue curSet idx ele | ele = IntSet.insert idx curSet
                                     | otherwise = curSet

-}



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
--TODO CONTINUE HERE
{-
Assuming the nr of agents it what scales up, I want to try to go though those only once (but it will be at best quadratic anway :/)
Assumin we have the SNM in the following form

data SNModel = SNM
 { positions :: M.Map Topic (Set Position) --the sets should be pairwise disjoint
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key
 , val :: M.Map Agent (M.Map Topic (Set Position)) --the dual
 } deriving (Eq, Show)

-}


{-
updSelecNew :: Double -> SNModel -> SNModel
updSelecNew 0 m = makeFullRelModel m
updSelecNew tau m@(SNM positions' _ val') = m {rel = newRel} where
....


-}

{-


TODO ACHTUNG this idea only works for the basic version, not the tweaked updates

new try: assuming nr agents >> 2^(nr positions per topic)
assume the following data structure:

data SNModel = SNM
 { agents :: AgentSet
 , positions :: M.Map Topic (Set Position) --the sets should be pairwise disjoint
 , rel :: M.Map Topic Relation --the social networks, every topic should be a key
 , val :: M.Map Topic (M.Map (Set Position) AgentSet) --full map over power set of positions in a topic, map to pariwise disjoint sets of agents, every agent is present
 } deriving (Eq, Show)

 data Relation = M.Map AgentSet (Set AgentSet)  --if we know nothing about equivalence classes yet, the keys are singleton sets like before and the values are singleton sets of a set if agents

-}

{-
updSelecNew :: Double -> SNModel -> SNModel
updSelecNew 0 m = makeFullRelModelNew m
updSelecNew tau m@(agents' _ oldRel val') = m {rel = foldlWithKey' constructRels M.empty val} where
    constructRels curRelMap tpc posAgs = M.union curRelMap (M.singleton tpc (constructRel posAgsList)) where
        constructRel [] = M.empty
        constructRel ((pos, ags):rest) =  M.unionWith S.union (thisPosPart pos ags rest) (construcRel rest)
        thisPosPart pos ags [] = M.empty
        thisPosPart pos ags ((pos2, ags2):rest) | similarPred pos pos2 = M.unionWith S.union (M.fromList [(ags, S.singleton ags2), (ags2, S.singleton ags)]) (thisPosPart pos ags rest)
                                            | otherwise  = thisPosPart pos ags rest
        similarPred pos pos2 = S.size (S.intersect pos pos2) --you can use tpc here :)
        posAgsList = M.toList posAgs

--construcRels :: M.Map Topic Relation -> Topic -> M.Map (Set Position) AgentSet -> M.Map Topic Relation

--idea for the new kind of data structure:
makeFullRelModelNew :: SNModel -> SNModel
makeFullRelModelNew m = m {rel = newRel} where
    newRel = M.fromList [(topic, fullRel) | topic <- M.keys positions]
    fullRel = M.singleton (agents, agents)
--TODO think about what this data structure would mean for formula evaluation of PrpF
--I think it would mean bad stuff :/ for both checks

-}
--TODO check if this works, changed it
--takes a SNModel and makes full relations for all topics
makeFullRelModel :: SNModel -> SNModel
makeFullRelModel m@(SNM agents' _ rel' _) = m { rel = M.map fullRel rel' } where
    fullRel = M.map allFriends
    allFriends _ = agents'

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

