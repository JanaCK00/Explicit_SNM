module TestHelpers where

import Syntax
import SNModel
import qualified Data.Map.Strict as M
--import Data.Map.Strict ((!))
import qualified Data.Set as S
--import Data.Set (Set)
--import Data.List as L
import Semantics

propo1 :: Form
propo1 = PrpF (Adopted (Ag "1") (Pos (Tpc "1") "1"))


--define some simple tautology
taut :: Form
taut = Disj [propo1, Neg propo1]


{-
check if a given SNModel maps every topic to a Relation and
in each Relation every agent to some set of friends (which may be empty)
-}
fullRel :: SNModel -> Bool
fullRel (SNM agents' positions' rel' _) = (M.size rel' == M.size positions') && fullRelAgs rel' where
    fullRelAgs = all (\x -> M.size x == S.size agents')


{-
check if a given SNModel maps every positions to a set of agents who have adopted it
(which may be empty)
-}
fullVal :: SNModel -> Bool
fullVal (SNM _ positions' _ val') = M.size val' == S.size (allPos positions')

--check if the set of agents in non-empty
nonEmptyAgs :: SNModel -> Bool
nonEmptyAgs = not . null . agents

--check if the set of topics in non-empty (by checking if the map isn't empty)
nonEmptyTpcs :: SNModel -> Bool
nonEmptyTpcs = not . null . positions

--check if the set of positions per topic in non-empty
nonEmptyPos :: SNModel -> Bool
nonEmptyPos = not . any null . positions

--check if the positions maps a topic to a set containing only positions of that topic
validPositions :: SNModel -> Bool
validPositions (SNM _ positions' _ _) =  all everyPos (M.toList positions') where
    everyPos (tpc, pos) = all (\p -> posTopic p == tpc) pos

{-}
--check if everything that used to be modeled as a set has no duplicates in list-form
noDuplicates :: SNModel -> Bool
noDuplicates (SNM agents' positions' rel' val') = noDups agents' && all noDups positions' && all (all noDups) rel' && all noDups val' where
    noDups l = S.toList l == nub (S.toList l) --TODO remove toList after I've changed it
-}

--check all properties at once
--TODO extend if I write more
isValidSNModel :: SNModel -> Bool
isValidSNModel snm = all (\f -> f snm) [fullRel, fullVal, nonEmptyAgs, nonEmptyPos, nonEmptyTpcs, validPositions]

--TODO find out how to get random rumbers in [0,1]
consecutiveSelec :: SNModel -> Bool
consecutiveSelec m = updSelec m 0.7 == updSelec (updSelec m 0.5) 0.7

--TODO find out how to get random rumbers in [0,1]
--test if an Infl after a Selec 1 doesn't change anything
consInflSelecOne :: SNModel -> Bool
consInflSelecOne m = updSelec m 1 == updInfl (updSelec m 1) 0.5


--TODO check if an application of Selec makes it reflexive and transitive
