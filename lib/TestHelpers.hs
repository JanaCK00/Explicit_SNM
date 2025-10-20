module TestHelpers where

import Syntax
import SNModel
import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import qualified Data.Set as S
import Data.Set (Set)


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