module Semantics where


--TODO only necessary imports
import Syntax ( Form(..), Prp(Connected, Adopted), UpOperator (Infl, Selec) )
import SNModel ( SNModel(rel, val, SNM))
import Data.Map.Strict ((!))
import qualified Data.Map as M
import qualified Data.Set as S
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import SetTheory (makeTransitive, makeReflexive, makeSymmetric)


-- Semantics defined on Formulas as defined in Syntax

--TODO do I have to use simplify here somewhere, if I want to make sure it's applied before we evaluate??
--but if I include it here, it will be done over and over again. Would it be best to write a function
--that is exposed to users, that doesn't directly use this, but rather one where I first use simplify and then this?
--same for a valid tau

(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (PrpF (Adopted agent position'))         = agent `IntSet.member` (val m ! position')
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


TODO is there an easy edge case??? I actually don't think so
with 0 it would be the full positions, if there wasn't the rule about empty neighbours, there it's only the existing ones
with 1 it be only those positions that are held by everone you're friends with.
    if that inlcudes you, it will be a subset of your existing positions

Properties:
 - NOT idempotent
 - in general it does not depend on the current positions (eg. it's not accumulative), but after a few steps the changes will probably be smaller?
 --TODO so i might make sense to use map manipulation?? but checking it takes the same time as inserting anway...

 THE PROBLEM is with both of these operators, that they depend on the other thing than they manipulate...
-}

--TODO rewrite
updInfl ::  Double -> SNModel -> SNModel
updInfl tau m@(SNM agents' positions' rel' val') = m { val = newVal } where
    newVal = M.unions [M.fromList [(p, thisPsAgs top p) | p <- S.toList $ positions' ! top] |  top <- M.keys positions']
    thisPsAgs top p = IntSet.filter (friendsThink top p) agents'
    friendsThink top p ag  | IntSet.size (n_T_i top ag) == 0  = ag `IntSet.member` (val' ! p)
                           | otherwise                        = fromIntegral (IntSet.size (IntSet.intersection (n_T_i top ag) (val' ! p) ))/ fromIntegral (IntSet.size (n_T_i top ag)) >= tau
    n_T_i top ag = (rel' ! top) ! ag --TODO is it a problem that this gets looked up many times?

{-}

--CONTINUE HERE
nehmen wir an wir haben neu ein val wie folgt
val :: M.Map Topic (M.Map Position AgentSet)


updInflNew ::  Double -> SNModel -> SNModel
updInflNew tau m@(SNM agents' rel' val') = m { val = newVal} where
    newVal = M.mapWithKey (myFunction agents') val'
    myFunction ags t posMap = foldr (subFunction t) posMap ags
    subFunction t ag posMap = M.foldrWithKey posMap --CONTINUE HERE
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

--TODO rewrite
--IDEA look at map manipulations or recursion to try and avoid list comprehension to avoid conversions to maps
--
updSelec::  Double -> SNModel -> SNModel
updSelec 0 m = makeFullRel m
updSelec tau m@(SNM agents' positions' _ val') = m {rel = newRel} where
    newRel = M.fromList [(t, thisTsRel t)| t <- M.keys positions']
    thisTsRel t = M.fromList [(ag, newFriends t ag)| ag <- IntSet.toList agents' ]
    newFriends t ag = IntSet.filter (pred_sim_T t ag) agents'
    pred_sim_T t ag ag2 = fromIntegral (S.size (sim_T t ag ag2)) / fromIntegral (S.size (positions' ! t)) >= tau
    sim_T t ag ag2 = S.filter (agree ag ag2) (positions' ! t)
    agree ag ag2 p = ag `IntSet.member` (val' ! p) && ag2 `IntSet.member` (val' ! p) ||
                           not (ag `IntSet.member` (val' ! p)) && not (ag2 `IntSet.member` (val' ! p))



--takes a SNModel and makes full relations for all topics
makeFullRel :: SNModel -> SNModel
makeFullRel m@(SNM agents' _ rel' _) = m { rel = newRel } where
    newRel = M.map fullRel rel'
    fullRel = M.map (agents' `IntSet.union`)

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

When in doubt: I could always implement the dynamics acc. to the recursion axioms in the interplay paper
-}

{-
TODO
usage in ghci
examleSmall |=
-}

