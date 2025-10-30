module Semantics where


--TODO only necessary imports
import Syntax ( Form(..), Prp(Connected, Adopted), UpOperator (Infl, Selec) )
import SNModel ( SNModel(rel, val, SNM), posTopic)
import Data.Map.Strict ((!))
import qualified Data.Map as M
import qualified Data.Set as S


-- Semantics defined on Formulas as defined in Syntax

--TODO do I have to use simplify here somewhere, if I want to make sure it's applied before we evaluate??
--but if I include it here, it will be done over and over again. Would it be best to write a function
--that is exposed to users, that doesn't directly use this, but rather one where I first use simplify and then this?
--same for a valid tau

(|=) :: SNModel -> Form -> Bool
(|=) _ Top                                      = True
(|=) _ Bot                                      = False
(|=) m (PrpF (Adopted agent position'))         = agent `S.member` (val m ! position')
(|=) m (PrpF (Connected topic agent1 agent2))   = agent2 `S.member`((rel m ! topic) ! agent1)
(|=) m (Neg f)                                  = not $ m |= f
(|=) m (Conj fs)                                = all (m |=) fs
(|=) m (Disj fs)                                = any (m |=) fs
(|=) m (Impl f g)                               = not (m |= f) || m |= g

(|=) m (Update (Infl tau) f)                    = (|=) (updInfl m tau) f
(|=) m (Update (Selec tau) f)                   = (|=) (updSelec m tau) f


{-
Performs the social influence operation on the model with the provided threshold.
Assumes tau is in [0,1].


TODO is there an easy edge case??? I actually don't think so
with 0 it would be the full positions, if there wasn't the rule about empty neighbours, there it's only the existing ones
with 1 it would be the existing positions, if there wasn't the fact that it's not necessarily refelxive

Properties:
 - NOT idempotent
-}

--TODO rewrite
updInfl :: SNModel -> Double -> SNModel
updInfl (SNM agents' positions' rel' val') tau = SNM agents' positions' rel' newVal where
    newVal = M.fromList [(p, thisPsAgs p)| p <- M.keys val']
    thisPsAgs p' = S.filter (friendsThink p') agents'
    friendsThink p'' ag  | S.size (n_T_i p'' ag) == 0  = ag `S.member` (val' ! p'')
                         | otherwise                   = fromIntegral (S.size (S.intersection (n_T_i p'' ag) (val' ! p'') ))/ fromIntegral (S.size (n_T_i p'' ag)) >= tau
    n_T_i p''' ag' = (rel' ! posTopic p''') ! ag'

{-
Performs the friendship selection operation on the model with the provided threshold.
Assumes tau is in [0,1].

TODO is there another easy edge case? I don't think so...

Properties:
 - produces reflexive and symmetric relations
 - idempotent with constant tau
 - application of two selec operation with different tau makes the first irrelevant
-}

--TODO rewrite
updSelec:: SNModel -> Double -> SNModel
updSelec m 0 = makeFullRel m
updSelec (SNM agents' positions' _ val') tau = SNM agents' positions' newRel val' where
    newRel = M.fromList [(t, thisTsRel t)| t <- M.keys positions']
    thisTsRel t' = M.fromList [(ag, newFriends t' ag)| ag <- S.toList agents' ]
    newFriends t'' ag' = S.filter (pred_sim_T t'' ag') agents'
    pred_sim_T t''' ag'' ag2 = fromIntegral (S.size (sim_T t''' ag'' ag2)) / fromIntegral (S.size (positions' ! t''')) >= tau
    sim_T t'''' ag''' ag2' = S.filter (agree ag''' ag2') (positions' ! t'''')
    agree ag'''' ag2'' p = ag'''' `S.member` (val' ! p) && ag2'' `S.member` (val' ! p) ||
                           not (ag'''' `S.member` (val' ! p)) && not (ag2'' `S.member` (val' ! p))



--takes a SNModel and makes full relations for all topics
makeFullRel :: SNModel -> SNModel
makeFullRel (SNM agents' positions' rel' val') = SNM agents' positions' newRel val' where
    newRel = M.fromList [(t, fullRels)| t <- M.keys rel']
    fullRels = M.fromList [(ag, agents')| ag <- S.toList agents' ]


{-
TODO OR should I just say the behaviour is undefined outside of this range? If someone were to provide
a too big number, it wouldnt work anywway...and I dont want to work with errors bc of the Maybe values
ALTERNATIVELY I could again work with an exposed function that returns an error to a user providing an
invalid number and internally work with the assumption that it's a valid one!!
Takes a double and returns a double in [0,1].
This allows for updates to work with tau outside of [0,1].
-}

--getDecimal :: Double -> Double
--getDecimal 1 = 1
--getDecimal t = t - floor t





{-

When in doubt: I could always implement the dynamics acc. to the recursion axioms in the interplay paper
-}

{-
TODO
usage in ghci
examleSmall |=
-}

