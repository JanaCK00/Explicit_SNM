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

import qualified Data.Vector.Mutable as MV
import Control.Monad.ST (runST)
import Syntax (Mode (Basic, Variant))



data CaseSNM = CSNM
    {snmodel :: SNModel
    , eliteList :: [Int]
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
publicNrAgs, eliteNrAgs, totalNrAgs, dBot, dCap, m0, restNr :: Int
publicNrAgs = 100 --100
eliteNrAgs = 20 --20
totalNrAgs = publicNrAgs + eliteNrAgs
dBot = 2--2 -- min out degree of newly added nodes
dCap = 20 -- 5 --max out degree of newly added nodes
m0 = 5--5 --size of starting network in generation
restNr = totalNrAgs - m0


allAgs :: [Agent]
allAgs = [0..totalNrAgs-1]

climate :: Topic
climate = T 1

incomePos, normPos, politicalPos :: Position
incomePos    = P 1
normPos      = P 2
politicalPos = P 3

npi, np, p :: Set Position
p   = S.singleton politicalPos
np  = S.fromList [normPos, politicalPos]
npi = S.fromList [incomePos, normPos, politicalPos]

--TODO positions for T 2
t2Positions :: Set Position
t2Positions = S.fromList [P 4, P 5, P 6]

propoIncome, propoNorm, propoPolitical :: Double
propoIncome = 0.69
propoNorm = 0.86
propoPolitical = 0.89

nrIncome, nrNorm, nrPolitical :: Int
nrIncome = computeProportion propoIncome
nrNorm = computeProportion propoNorm
nrPolitical = computeProportion propoPolitical
computeProportion propo = floor (propo * fromIntegral publicNrAgs)


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
    getPos i | i<= largestIncome    = npi
             | i<= largestNorm      = np
             | otherwise            = p

-}

posMapCase :: M.Map Topic (Set Position)
posMapCase = M.fromList [(T 1, npi), (T 2, S.fromList [P 4, P 5, P 6])]


initialCore :: [[Int]]
initialCore = replicate m0 [0..m0-1]




--takes current relation and the nr of agents to still be added
--add new nodes with preferential attachment
preferentialAttachment :: [[Int]] -> Int -> Gen [[Int]]
preferentialAttachment cur 0 = return $ reverse cur --here we can directly take care of reversing (and as in the beginning the core is symmetric, it shouldn't matter)
preferentialAttachment cur i = do
    let n = length cur --n is at the same time the name of the agent we are currently adding
        --TODO maybe store the in-degree in a counter, so I don't have to go through it every time?
        inDegreeAgs = (concatMap (replicate 2) [0..n]) ++ concat cur --makes sure all existing nodes show up at least once (including the new node itself), and proportional to their in-degree
    thisAgsFriends <- sublistOfLength dBot dCap inDegreeAgs
    --inDegree <- sublistOfLength 0 dCap [0..n-1]  --TODO CONTINUE HERE optionally have some existing nodes attach to the new node, bc the average in-degree of public nodes is ridiculosly low. note that these will not be the final names of the agents, bc the intermediate list is reversed
    preferentialAttachment (thisAgsFriends : cur) (i-1) --ACHTUNG like this we have to reverse the final thing, but we save time

--TODO maybe store in- and out-degree, so I don't have to go though it every time
--ACTUALLY: This doesn't have to be efficient :) it's just for my use. So don't waste time on that


{-- UNCOMMENT HERE

data Action = NewEdge | NodeIngoing | NodeOutgoing deriving (Eq, Show)
type DegRelation = Vector (IntSet, Int, Int) --neighbors, in-degree, out-degree

fst3 :: (a, b, c) -> a
fst3 (i, _, _) = i

--takes nr of nodes to be added in total
--we could introduce a break here, if it becomes to long we only pick node-adding actions
getActionList :: Int -> Gen[Action]
getActionList 0 = return []
getActionList n = do
    newAction <- pickAction <$> genDouble
    if newAction == NewEdge
        then do rest <- getActionList n
        else do rest <- getActionList (n-1)
    return (newAction : rest)


pickAction :: Double -> Action
pickAction d | d<= probEdge = NewEdge
             | d<= probEdge + probOutgoing = NodeOutgoing
             | otherwise = NodeinGoing


--TODO look up the numbers in the paper or try them out
probEdge, probOutgoing, probIngoing :: Double
probOutgoing = 0.4 --alpha
probEdge = 0.4 --beta --TODO this shouldn't be too high, so we don't take to many steps until we have added enough nodes...
probIngoing = 0.2 --gamma

--TODO do I have to use mutable vectors? It's a bit complicated to only thaw once, when muddled with Gen
--TODO think about how I could pregenerate everything (including what I need to choose proportionally to in-/out-degree)
--takes list of Actions, current DegRelation, next Agent to be added
executeActions ::[Action] -> DegRelation -> Int -> Gen Relation
executeActions [] _ _            = return $ V.map fst3 cur --if action lists is empty, we are done
executeActions (x:xs) cur thisAg = do
    if x == NewEdge
        then do i <- pickOutgoing cur
                j <- pickIngoing cur
                let newCur = addEdge cur i j ----TODO update in-and out-degree counters
                executeActions xs newCur thisAg
        else if x == NodeIngoing
            then do i <- pickOutgoing
                    let newCur = addEdge cur i thisAg
                    executeActions xs newCur (thisAg + 1)
            else do j <- pickIngoing
                    let newCur = addEdge cur thisAg j
                    executeActions xs newCur (thisAg + 1)

directedPrefAttach :: Gen Relation
directedPrefAttach = do
    let startDegRel = V.replicate m0 (IntSet.fromList [0..m0-1], m0, m0) --ACHTUNG später brauche ich dass die degs nicht 0 sind
    actions <- getActionList restNr
    executeActions actions startDegRel m0

{-
--Takes DegRelation, Agent1, Agent2, return relation with added edge from Agent1 to Agent2 and updated deg counts
addEdge :: DegRelation -> Agent -> Agent -> Relation
addEdge cur i j | i isIn j = cur
                | otherwise = cur \\
                    where
                        (isIn) k l = k IntSet.member (cur V.! j)
-}


- UNCOMMENT HERE -}

sublistOfLength :: Ord a => Int -> Int -> [a] -> Gen [a]
sublistOfLength lmin lmax xs = do
    thisL <- chooseInt (lmin,lmax)
    subListRec thisL xs

subListRec :: Eq a => Int -> [a] -> Gen [a]
subListRec 0 _ = return []
subListRec i xs = do
    if null xs then return [] --elements throws error if xs is empty
        else do el <- elements xs
                rest <- subListRec (i-1) $ filter (/= el) xs --assuming we don't choose with replacement
                return $ el:rest


constructClimateRel :: Gen (Relation, [Int])
constructClimateRel = do
    let nrToAdd = totalNrAgs - m0
    climateLList <- preferentialAttachment initialCore nrToAdd
    let climateRelRaw = V.map IntSet.fromList $ V.fromList climateLList
        (_, elite') = findKrich eliteNrAgs climateRelRaw
        climateRelElite = prepareElite elite' climateRelRaw
    return (climateRelRaw, elite') --return (climateRelElite, elite') --TODO CONTINUE HERE; changed this to exclude manuel elite preparation


--TODO maybe skip this step
--remove all outgoing edges from elite, then make elite fully connected
prepareElite:: [Int] -> Relation -> Relation
prepareElite elite' rel' = V.update_ rel' indexVec valueVec where
    indexVec =  V.fromList elite'
    valueVec = V.replicate eliteNrAgs $ IntSet.fromList elite'

--TODO
--increase density in public
{-connectPublic :: [Int] -> Relation -> Gen Relation
connectPublic
-}

constructRelMap :: Gen (M.Map Topic Relation, [Int])
constructRelMap = do
    (relT2, _) <- preferentialAttachment initialCore (totalNrAgs-m0)--randomRel totalNrAgs --TODO maybe leave this out completely for the initial model? or make it sparser. but if the public is sparsely connected, restricted friendship selection will be a problem
    (climateRel, elite') <- constructClimateRel
    return (M.fromList [(T 1, climateRel), (T 2, relT2)], elite')


--takes List of public, returns climate dual
constructClimateDual :: [Int] -> Gen (IntMap (Set Position))
constructClimateDual public' = do
    takePolitical <- sublistOfLength nrPolitical nrPolitical public'
    takeNorm <- sublistOfLength nrNorm nrNorm takePolitical
    takeIncome <- sublistOfLength nrIncome nrIncome takeNorm
    let politicalMap = L.foldl' (\cur k -> IntMap.insert k p cur) IntMap.empty takePolitical
        normMap = L.foldl' (\cur k -> IntMap.insert k np cur) politicalMap takeNorm --value will be replaced for existing keys
    return $ L.foldl' (\cur k -> IntMap.insert k npi cur) normMap takeIncome

--take list of public
constructDualMap :: [Int] -> Gen (M.Map Topic (IntMap (Set Position)))
constructDualMap public' = do
    dualT2 <- randomDualT t2Positions allAgs
    dualClimate <- constructClimateDual public'
    return $ M.fromList [(T 1, dualClimate), (T 2, dualT2)]


instance Arbitrary CaseSNM where
  arbitrary = do
    (rel', elite') <- constructRelMap
    let public' = allAgs L.\\ elite'
    dual' <- constructDualMap public'
    return (CSNM (SNM totalNrAgs posMapCase rel' dual') elite') --elite will be ordered in ascening order of nr in-degree


makeCSNMRandomRel :: Gen CaseSNM
makeCSNMRandomRel = do
    rel1 <- randomRel 120
    rel2 <- randomRel 120
    let (public', elite') = findKrich eliteNrAgs rel1
        rel' = M.fromList [(T 1, rel1), (T 2, rel2)]
    dual' <- constructDualMap public'
    return (CSNM (SNM totalNrAgs posMapCase rel' dual') elite')

--takes Climate Dual, List of Elite, returns nr of agents from public holding each position (political, norm, income)
majorityVote :: IntMap (Set Position) -> [Int] -> (Int, Int, Int)
majorityVote dual_t elite' = IntMap.foldlWithKey' increaseCounter (0,0,0) dual_t where
    increaseCounter count ag set | ag `notElem` elite' = S.foldl' increaseAccording count set
                                 | otherwise = count --only count the positions of the public
    increaseAccording (i, j, k) elem' | elem' == politicalPos = (i+1, j, k)
                                      | elem' == normPos = (i, j+1, k)
                                      | otherwise = (i, j, k+1)





--TODO test


--takes Mode of Selec, Mode of Infl, CaseSNM
--returns SNM after interleaving of the two has converged, incl the number of steps until convergence
runInterleaving :: Mode -> Mode -> CaseSNM -> (SNModel, Int)
runInterleaving Basic Basic (CSNM snm elite') = (fixCount (( updSelecBasic 0.5). (updInflBasic  0.5)) snm)
runInterleaving Basic Variant (CSNM snm elite') = (fixCount (( updSelecBasic 0.5). (updInflVariant  0.5)) snm)
runInterleaving Variant Basic (CSNM snm elite') = (fixCount (( updSelecVariant 0.5). (updInflBasic  0.5)) snm)
runInterleaving Variant Variant (CSNM snm elite') = (fixCount (( updSelecVariant 0.5). (updInflVariant  0.5)) snm)


runExperiment :: Mode -> Mode -> CaseSNM -> IO()
runExperiment selecMode inflMode m@(CSNM snm elite') = do
    let (initAvgOutPublic, initAvgInPublic, initAvgOutElite, initAvgInElite) = averageDegreesCSNModel m
        (finalModel, steps) = runInterleaving selecMode inflMode m
        finalClimateDual = (dual finalModel) M.! (T 1)
        (polNr, normNr, incomeNr) = majorityVote finalClimateDual elite'
        (finalAvgOutPublic, finalAvgInPublic, finalAvgOutElite, finalAvgInElite) = averageDegreesCSNModel (CSNM finalModel elite')
    putStr $ "You ran " ++ show selecMode ++ "Selec on " ++ show inflMode ++ "Infl. \n The starting Model has " ++ show eliteNrAgs ++ " Elite nodes and " ++ show publicNrAgs ++
                " Public nodes. \n Following initial average degrees: \n Average OutDegree Public: " ++ show initAvgOutPublic ++ "\n Average InDegree Public: " ++ show initAvgInPublic ++
                "\n Average OutDegree Elite: " ++ show initAvgOutElite ++ "\n Average InDegree Elite: " ++ show initAvgInElite ++ "\n The experiment converged after " ++
                show steps ++ " steps. \n Following final average degrees: \n Average OutDegree Public: " ++ show finalAvgOutPublic ++ "\n Average InDegree Public: " ++
                show finalAvgInPublic ++ "\n Average OutDegree Elite: " ++ show finalAvgOutElite++ "\n Average InDegree Elite: " ++ show finalAvgInElite ++
                "\n The majority vote in the final model is as follows. \n Public nodes holding political action: " ++ show polNr ++ "\n Public nodes holding social norm: " ++ show normNr ++
                "\n Public nodes holding income contribution: " ++ show incomeNr ++ "\n"


--CaseSNM, returns (avgOutPublic, avgInPublic, avgOutElite, avgInElite)
averageDegreesCSNModel :: CaseSNM -> (Double, Double, Double, Double)
averageDegreesCSNModel (CSNM (SNM _ _ rel' _) elite') = averageDegrees (rel' M.! (T 1)) elite'

--Relation,  returns (avgOutPublic, avgInPublic, avgOutElite, avgInElite)
averageDegreesfromRel :: Relation -> (Double, Double, Double, Double)
averageDegreesfromRel rel' = averageDegrees rel' elite' where
    elite' = snd $ findKrich eliteNrAgs rel'

--Relation, list of elite, returns (avgOutPublic, avgInPublic, avgOutElite, avgInElite)
averageDegrees :: Relation -> [Int] -> (Double, Double, Double, Double)
averageDegrees rel' elite' = (avgOutPublic, avgInPublic, avgOutElite, avgInElite) where
    outdegreeVector = V.map IntSet.size rel'
    indegreeMap = countOccur $ concatMap IntSet.toList rel'
    (totalOutPublic, totalOutElite) = V.ifoldl' addUp (0, 0) outdegreeVector
    (avgOutPublic, avgOutElite) = averagePair totalOutPublic totalOutElite
    (totalInPublic, totalInElite) = M.foldlWithKey' addUp (0, 0) indegreeMap
    (avgInPublic, avgInElite) =  averagePair totalInPublic totalInElite
    addUp (curP, curE) idx nrFriends | idx `notElem` elite' = (curP + nrFriends, curE )
                                     | otherwise = (curP , curE + nrFriends)
    averagePair i j = (fromIntegral i / fromIntegral publicNrAgs, fromIntegral j / fromIntegral eliteNrAgs)




--usage in ghci:
{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel
-}
--averageDegreesCSNModel <$> (generate arbitrary :: IO CaseSNM)