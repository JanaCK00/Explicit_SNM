module Semantics where


--TODO necessary imports
import Syntax
import SNModel -- TODO restrict?
import qualified Data.Map.Strict as M -- TODO do I need it here?
import Data.Map.Strict ((!))
import qualified Data.Set as S


-- Semantics defined on Formulas as defined in Syntax

(|=) :: SNModel -> Form -> Bool
(|=) _ Top = True
(|=) _ Bot = False
(|=) m (PrpF (Adopted agent position)) = agent `S.member` (val m ! position)
(|=) m (PrpF (Connected topic agent1 agent2)) =  agent2 `S.member`((rel m ! topic) ! agent1)
(|=) m (Xor f g) = m |= Disj [Conj [f, Neg g], Conj [Neg f, g]] --TODO needed?
(|=) m (Neg f) = not $ m |= f
(|=) m (Conj fs)  = all (m |=) fs
(|=) m (Disj fs)  = any (m |=) fs
(|=) m (Impl f g) = not (m |= f) || m |= g --TODO needed?
(|=) m (Equiv f g) = m |= Conj [Impl f g, Impl g f]-- TODO needed? (I actually don't think so ;))
(|=) m (Cross tau f) = False --TODO are just already here for pattern exhaustion, maybe rename
(|=) m (Hash tau t) = False
--TODO dynamics
{-
(|=) m (Cross tau f) = ... --TODO somehow restrict tau
(|=) m (Hash tau f) = ...
-}



--TODO do I need to do something with validity ? (holds on all SNModels? - page 74 of interplay paper)