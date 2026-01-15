module CaseStudy where

import SNModel
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf  )
import SetTheory (Agent, Relation)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as M

newtype CaseSNM = CSNM SNModel deriving (Eq, Show)

--Question: do it with quickcheck? have to have a seed so all scnearios use the same test cases?
--genereate model, run until stable (if not stable after fixed nr of turn, stop), check proportion of public who hold climate positions

--CHANGE if needed
publicNrAgs, eliteNrAgs, totalNrAgs :: Int
publicNrAgs = 100
eliteNrAgs = 20
totalNrAgs = publicNrAgs + eliteNrAgs

publicAgs, eliteAgs, allAgs :: [Agent]
publicAgs = [0..publicNrAgs-1]
eliteAgs = [publicNrAgs .. eliteNrAgs-1]
allAgs = [0..totalNrAgs-1]

climate :: Topic
climate = T 1

incomePos, normPos, politicalPos :: Position
incomePos    = P 1
normPos      = P 2
politicalPos = P 3

inp, np, p :: Set Position
p   = S.singleton politicalPos
np  = S.fromList [normPos, politicalPos]
inp = S.fromList [incomePos, normPos, politicalPos]

--TODO positions for T 2
t2Positions :: Set Position
t2Positions = S.fromList [P 4, P 5, P 6]

propoIncome, propoNorm, propoPolitical :: Double
propoIncome = 0.69
propoNorm = 0.86
propoPolitical = 0.89


--we assume that the positions are accumulative TODO probably not the right word
dualClimate :: IntMap (Set Position)
dualClimate = IntMap.fromDistinctAscList [(i, getPos i) | i <- [0..largestPolitical] ] where
    getPos i | i<= largestIncome    = inp
             | i<= largestNorm      = np
             | otherwise            = p
    largestIncome =  computeLargest propoIncome
    largestNorm = computeLargest propoNorm
    largestPolitical = computeLargest propoPolitical
    computeLargest propo = floor (propo * fromIntegral publicNrAgs) - 1


posMap :: M.Map Topic (Set Position)
posMap = M.fromList [(T 1, inp), (T 2, S.fromList [P 4, P 5, P 6])]


--TODO
--copied from SNModel.hs
{-randomRelMap :: Int -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap nrAgs (t:tpcs) =  do
    thisTpcsRel <- randomRel nrAgs
    rest <- randomRelMap nrAgs tpcs
    return $ M.insert t thisTpcsRel rest
-}

{-constructRelMap :: Gen (M.Map Topic Relation)
constructRelMap = do
    randomRelMap

-}
--TODO FIND OUT HOW TO DO THIS SMARTLY; probably read the background literature first :)

constructDualMap :: Gen (M.Map Topic (IntMap (Set Position)))
constructDualMap = do
    dualT2 <- randomDualT t2Positions allAgs
    return $ M.fromList [(T 1, dualClimate), (T 2, dualT2)]

{-

instance Arbitrary CaseSNM where
  arbitrary = do
    rel' <- constructRelMap
    dual' <- constructDualMap
    return (CSNM (SNM totalNrAgs posMap rel' dual'))

    -}