module Types where
import Data.IntSet (IntSet)
import Data.Vector
import qualified Data.Vector as V
import qualified Data.IntSet as IntSet
import SMCDEL.Internal.Help (lfp)



{-
This module defines types for topics, positions, agents and relations.
It also provides some helper functions on Relations.
-}


{-
Data representation for topics, positions, agents and relations.
-}
newtype Topic = T Int deriving (Eq, Show, Ord)
newtype Position = P Int deriving (Eq, Show, Ord)
type Agent = Int
type AgentSet = IntSet

{-
A Relation represents a directed binary relation in the form of a vector of adjacency sets.
At the i-tn index we store the set of friends of agent i.
-}
type Relation = Vector AgentSet



--Given a Relation, makes it reflexive.
makeReflexive :: Relation -> Relation
makeReflexive = V.imap IntSet.insert



--Given a Relation, makes it symmetric.
makeSymmetric :: Relation -> Relation
makeSymmetric rel' = makeSym 0 (V.toList rel') rel' where
  makeSym _ [] acc = acc
  makeSym i (ifriends:rest) acc = makeSym (i+1) rest (V.imap addMe acc) where
    addMe a f | a `IntSet.member` ifriends = IntSet.insert i f
              | otherwise                 = f

{-
  Recursively makes a given relation transitive. For each agent, given their current
  friends group, add all agents reachable from any friend in their friends group
  until a fixpoint is reached.
-}
makeTransitive :: Relation -> Relation
makeTransitive rel' = lfp makeTransOnce rel' where
  makeTransOnce = V.map addRel
  addRel val' = IntSet.unions [rel' V.! w | w <- IntSet.toList val'] `IntSet.union` val'


--Forms the union of two relations.
combineRelation :: Relation -> Relation -> Relation
combineRelation = V.zipWith IntSet.union


--Checks if a relation is symmetric.
isSym :: Relation -> Bool
isSym rel' = rel' == makeSymmetric rel'


--Checks if a relation is reflexive.
isRefl :: Relation -> Bool
isRefl = V.ifoldl' (\acc i friends -> acc && IntSet.member i friends) True


--Check if a relation contains no self-loops.
noSelfLoops :: Relation -> Bool
noSelfLoops = V.ifoldl' (\acc i friends -> acc && IntSet.notMember i friends) True


