module CaseStudy where

import SNModel
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf, chooseInt, elements  )
import SetTheory (Agent, Relation)
import Data.Set (Set)
import qualified Data.Set as S
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import qualified Data.List as L
import Semantics

data CaseSNM = CSNM
    {snm :: SNModel
    , elite :: [Int]
    }deriving (Eq, Show)

--Question: do it with quickcheck, combine all test parameters into one counting thing to have it run on the same test cases
--genereate model, run until stable (if not stable after fixed nr of turn, stop), check proportion of public who hold climate positions


--ACHTUNG: If I want to truly random models, and then choose the k top degree ones, I can't do the dual this easily^^
--for random, also I shoudl probably use some p Erdős–Rényi model.
--In this model, the network  is constructed as a randomly chosen n-node graph from the class
--Gn,p , where for every two nodes x, y, a link xy exists in the graph  with probability p,
--independently of the other links
--TODO WHAT is the p in my arbitrary generation right now?? 1/2???

--CHANGE if needed
publicNrAgs, eliteNrAgs, totalNrAgs, dBot, dCap, m0 :: Int
publicNrAgs = 100 --100
eliteNrAgs = 20 --20
totalNrAgs = publicNrAgs + eliteNrAgs
dBot = 2--2 -- min out degree of newly added nodes
dCap = 5 -- 5 --max out degree of newly added nodes
m0 = 5--5 --size of starting network in generation


allAgs :: [Agent]
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




{-
Takes an Int and a Relation, return a tuple (List of Public, List of Elite)
where elite are the k nodes of highest in-degree. For a tie, there is no defined rule TODO do I have to change this?
-}

findKrich :: Int -> Relation -> ([Int], [Int])
findKrich k v = splitAt (l-k) $ map fst $ L.sortOn snd $ M.toList freqMap where
    l = V.length v --number of agents 0...l-1
    freqMap = M.union occuring zeroMap --add agents with zero in-degree
    occuring = countOccur $ concatMap IntSet.toList v
    zeroMap = M.fromList [(i,0) | i <- [0..l-1]]


--ACHTUNG ones with zero connections shouldn't have zero probability to get connected to, so we add them once anyways
--maybe add reciprocity with some probability? otherwise old ones will never follow newer ones

--TODO adapt
--we assume that the positions are hierarchichal in the INITIAL model
{-
dualClimate :: [Int] -> IntMap (Set Position)
dualClimate public = IntMap.fromDistinctAscList [(i, getPos i) | i <- [0..largestPolitical] ] where
    getPos i | i<= largestIncome    = inp
             | i<= largestNorm      = np
             | otherwise            = p
    largestIncome =  computeLargest propoIncome
    largestNorm = computeLargest propoNorm
    largestPolitical = computeLargest propoPolitical
    computeLargest propo = floor (propo * fromIntegral publicNrAgs) - 1
-}

posMapCase :: M.Map Topic (Set Position)
posMapCase = M.fromList [(T 1, inp), (T 2, S.fromList [P 4, P 5, P 6])]


initialCore :: [[Int]]
initialCore = replicate m0 [0..m0-1]




--takes current relation and the nr of agents to still be added
--add new nodes with preferential attachment
preferentialAttachment :: [[Int]] -> Int -> Gen [[Int]]
preferentialAttachment cur 0 = return $ reverse cur --here we can directly take care of reversing (and as in the beginning the core is symmetric, it shouldn't matter)
preferentialAttachment cur i = do
    let n = length cur --n is at the same time the name of the agent we are currently adding
        inDegreeAgs = [0..n] ++ concat cur --makes sure all existing nodes show up at least once (including the new node itself), and proportional to their in-degree
    thisAgsFriends <- sublistOfLength dBot dCap inDegreeAgs
    --inDegree <- sublistOfLength 0 dCap [0..n-1]  --TODO CONTINUE HERE optionally have some existing nodes attach to the new node, bc the average in-degree of public nodes is ridiculosly low. note that these will not be the final names of the agents, bc the intermediate list is reversed
    preferentialAttachment (thisAgsFriends : cur) (i-1) --ACHTUNG like this we have to reverse the final thing, but we save time


--TODO get from List of Lists to Vector IntSet

sublistOfLength :: Ord a => Int -> Int -> [a] -> Gen [a]
sublistOfLength lmin lmax xs = do
    thisL <- chooseInt(lmin,lmax)
    subListRec thisL xs

subListRec :: Eq a => Int -> [a] -> Gen [a]
subListRec 0 _ = return []
subListRec i xs = do
    el <- elements xs --needs non-empty xs
    rest <- subListRec (i-1) $ filter (/= el) xs --assuming we don't choose the same one multiple times
    return $ el:rest


constructClimateRel :: Gen (Relation, [Int])
constructClimateRel = do
    let nrToAdd = totalNrAgs - m0
    climateLList <- preferentialAttachment initialCore nrToAdd
    let climateRelRaw = V.map IntSet.fromList $ V.fromList climateLList
        (_, elite) = findKrich eliteNrAgs climateRelRaw
        climateRelElite = prepareElite elite climateRelRaw
    return (climateRelElite, elite)

prepareElite:: [Int] -> Relation -> Relation
prepareElite elite' rel' = V.update_ rel' indexVec valueVec where
    indexVec =  V.fromList elite'
    valueVec = V.replicate eliteNrAgs $ IntSet.fromList elite'


    {-mapWithIndex replaceIfElite rel where
    replaceIfElite | ag IntSet.member eliteSet = eliteSet
                   | otherwise = id
    eliteSet = IntSet.fromList elite
    -}
--use thaw and freeze to set at every elite node the outgoing ones the set of elite nodes


constructRelMap :: Gen (M.Map Topic Relation, [Int])
constructRelMap = do
    relT2 <- randomRel totalNrAgs
    (climateRel, elite) <- constructClimateRel
    return $ (M.fromList [(T 1, climateRel), (T 2, relT2)], elite)


--TODO
constructClimateDual :: Gen (IntMap (Set Position))
constructClimateDual = return IntMap.empty --TODO

constructDualMap :: Gen (M.Map Topic (IntMap (Set Position)))
constructDualMap = do
    dualT2 <- randomDualT t2Positions allAgs
    dualClimate <- constructClimateDual
    return $ M.fromList [(T 1, dualClimate), (T 2, dualT2)]


instance Arbitrary CaseSNM where
  arbitrary = do
    (rel', elite') <- constructRelMap
    dual' <- constructDualMap
    return (CSNM (SNM totalNrAgs posMapCase rel' dual') elite') --elite will be ordered in ascening order of nr in-degree



--TODO test

averageDegreesCSNModel :: CaseSNM -> (Double, Double, Double)
averageDegreesCSNModel (CSNM (SNM _ _ rel' _) elite') = averageDegrees (rel' M.! (T 1)) elite'

--Relation, list of elite, returns (avgOutPublic, avgInPublic, avgInElite)
averageDegrees :: Relation -> [Int] -> (Double, Double, Double)
averageDegrees rel' elite' = (avgOutPublic, avgInPublic, avgInElite) where
    outdegreeVector = V.map IntSet.size rel'
    indegreeMap = countOccur $ concatMap IntSet.toList rel'
    avgOutPublic = fromIntegral (V.ifoldl' addIfPublic 0 outdegreeVector) / fromIntegral publicNrAgs
    addIfPublic cur idx nrFriends | ((not . elem idx) elite') = cur + nrFriends
                                  | otherwise = cur
    (totalInPublic, totalInElite) = (M.foldlWithKey' addUp (0, 0) indegreeMap)
    (avgInPublic, avgInElite) = (fromIntegral totalInPublic / fromIntegral publicNrAgs, fromIntegral totalInElite / fromIntegral eliteNrAgs)
    addUp (curP, curE) idx nrFriends | ((not . elem idx) elite') = (curP + nrFriends, curE )
                                     | otherwise = (curP , curE +nrFriends)


--usage in ghci:
--averageDegreesCSNModel <$> (generate arbitrary :: IO CaseSNM)