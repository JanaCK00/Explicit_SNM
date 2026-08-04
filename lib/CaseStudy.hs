module CaseStudy where

import SNModel
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , sublistOf, chooseInt, elements)
import Test.QuickCheck.Gen (genDouble)
import SetTheory (Agent, Relation)
import Data.Set (Set)
import qualified Data.Set as S
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
--import qualified Data.Vector.Mutable as MV
import qualified Data.List as L
import Semantics

--import qualified Data.Vector.Mutable as MV
--import Control.Monad.ST (runST)
import Syntax (Mode (Basic, Variant))



data CaseSNM = CSNM
    {snmodel :: SNModel
    , eliteList :: [Int]
    }deriving (Eq, Show)

--Question: do it with quickcheck, combine all test parameters into one counting thing to have it run on the same test cases
--genereate model, run until stable (if not stable after fixed nr of turn, stop), check proportion of public who hold climate positions



--define necessary parameters
--CHANGE if needed
publicNrAgs, eliteNrAgs, totalNrAgs, m0Param, mParam, nParam, aParam  :: Int
threshold, pTParam :: Double
--Define fixed parameters
totalNrAgs = 120    --number of agents in the generated networks
eliteNrAgs = 20     --TODO incoporate as a variable -> whereever it shows up, replace it with a parameter
publicNrAgs = totalNrAgs - eliteNrAgs --TODO incorporate as a variable
threshold = 0.5

{-
Fixed parameters for network generation (Holme-Kim)
-}
m0Param = 3         --size of starting network in generation
mParam = 3          --number of edges added per node in network generation
nParam = totalNrAgs --number of nodes in final network generated
pTParam = 0.5       --probability of a TF step
aParam = 1          --initial attractiveness



allAgs :: [Agent]
allAgs = [0..totalNrAgs-1]


--the topics in the case study
climate, artInt :: Topic
climate = T 1
artInt = T 2


--the four positions in the case study
incomePos, normPos, politicalPos, aiReg :: Position
incomePos    = P 1
normPos      = P 2
politicalPos = P 3
aiReg        = P 4


--different sets of positions
npi, np, p, t2Positions :: Set Position
p           = S.singleton politicalPos
np          = S.fromList [normPos, politicalPos]
npi         = S.fromList [incomePos, normPos, politicalPos]
t2Positions = S.singleton aiReg

--assigning positions to topics
posMapCase :: M.Map Topic (Set Position)
posMapCase = M.fromList [(T 1, npi), (T 2, t2Positions)]


{-
Computes the integer number corresponding to a given proportion of a total (rounded down)
-}
computeProportion :: (RealFrac a1, Integral b, Integral a2) => a1 -> a2 -> b
computeProportion propo ags = floor (propo * fromIntegral ags)

{-
Defining proportions that hold each position.
These are the numbers from the literature.
-}
propoIncome, propoNorm, propoPolitical, propoReg :: Double
propoIncome = 0.69    -- of public
propoNorm = 0.86      -- of public
propoPolitical = 0.89 -- of public
propoReg = 0.7        -- of all nodes


{-
For a specific network size, compute the number of nodes who will hold the position
according to the defined proportions.
-}
nrIncome, nrNorm, nrPolitical, nrReg :: Int
nrIncome = computeProportion propoIncome publicNrAgs        --number of public nodes holding positions incomePos
nrNorm = computeProportion propoNorm publicNrAgs            --number of public nodes holding positions normPos
nrPolitical = computeProportion propoPolitical publicNrAgs  --number of public nodes holding positions politicalPos
nrReg = computeProportion propoReg totalNrAgs               --number of all nodes holding positions aiReg (elite has same distribution as public)


{-
Input
k: absolute size of elite
Relation

Finds the k highest degree nodes (elite) and
returns tuple of (List of public, List of elite)

(For a tie, there is no defined rule.)
-}

findKrich :: Int -> Relation -> ([Int], [Int])
findKrich k v = splitAt (l-k) $ map fst $ L.sortOn snd $ M.toList freqMap where
    l = V.length v                                     --number of agents 0...l-1
    freqMap = M.union occuring zeroMap                 --add agents with zero in-degree (left-biased union)
    occuring = countOccur $ concatMap IntSet.toList v  --count in-degree of all agents with >0 neighbors
    zeroMap = M.fromList [(i,0) | i <- [0..l-1]]



{-
Constructs a fully connected network of a given size. (no self-loops)
-}

initialCore :: Int -> [[Int]]
initialCore m_0 = initialCoreRec 0 where
    initialCoreRec  step | m_0 == step = []
                         | otherwise = filter (/= step) [0..(m_0-1)] : initialCoreRec (step + 1)



--TODO: write tests

{-
Generates a Holme-Kim relation
Input:
N:            number of nodes in final network. -> TODO probably 120
m:            number of edges added per new node -> TODO probably 3
m ≤ m_0 < N : number of initial nodes -> TODO probably 3
p_t :         probability of a triad formation (TF) step -> TODO start with 0.5
A :           initial attractiveness for preferential attachment (PA) -> TODO start with 1
-}
holmeKim :: Int -> Int -> Int -> Double -> Int -> Gen Relation
holmeKim n m m_0 = holmeKimRec (n-m_0) m cur where
    cur = initialCore m_0

{-
Recursively genereate Holme-Kim relation
Input:
Number of remaining nodes to add
m: Number of edges to add per new node
Current Relation
p_t: probability of triad formation (TF) step
att: initial attractiveness

If no nodes remain, return the constructed relation.
Otherwise execute one PA step, then generate a sequence of PA/TF steps (length m-1) and execute them.
Then recursively finish the construction.
-}
holmeKimRec :: Int -> Int -> [[Int]] -> Double -> Int -> Gen Relation
holmeKimRec 0 _ cur _ _ = return $ translate cur
holmeKimRec n m cur p_t att = do
    let curExt = cur ++ [[]] --we have an empty list to store the neighbors of newNode in
    (cur_1, lastPA) <- paStep curExt att
    step_list <- getStepList [] p_t (m-1)
    new_cur <- doSteps step_list (cur_1,lastPA) att
    holmeKimRec (n-1) m new_cur p_t att


{-
Data type for both types of steps in Holme-Kim generation.
PAStep is a preferential attachement step.
TFStep is a triad formation step.
-}
data Step = PAStep | TFStep deriving (Eq, Show)


{-
Generates a sequence of steps.

Input:
p_t: probability of TF step
l: length of sequence to be generated
-}
getStepList :: [Step] -> Double -> Int -> Gen [Step]
getStepList xs _ 0 = return xs
getStepList xs p_t l = do
    newStep <- pickStep p_t <$> genDouble
    getStepList (newStep : xs) p_t (l-1)


{-
Input: p_t, d' (random double in range [0,1])
Returns TFStep if d<= p_t
-}
pickStep :: Double -> Double -> Step
pickStep p_t d'   | d' <= p_t = TFStep
                  | otherwise = PAStep


{-
Input:
list of steps
tuple of (current network, last node connected to in PA)
a: Initial attractiveness

Output: Executes steps from left to right and returns network.
-}
doSteps :: [Step] -> ([[Int]], Int) -> Int -> Gen [[Int]]
doSteps [] (cur, _) _ = return cur
doSteps (next:steps) (cur, lastPA) att = do
    if next == PAStep
    then do
        new_cur <- paStep cur att
        doSteps steps new_cur att
    else do
        new_cur <- tfStep (cur, lastPA) att
        doSteps steps new_cur att

{-
Executes one PA step for the newest node.
Chooses a non-neighbor node v to connect to with probability (degree v + A) / (sum over all nodes w in 0..newNode-1 (degree w + A))
Input:
current network
A: initial attractiveness
Output:
(New network, node that attached in PA step)
-}
paStep ::[[Int]] -> Int -> Gen ([[Int]], Int)
paStep cur att = do
    let newNode = length cur - 1
        nonOptions = newNode : last cur
        choices = concatMap (replicate att) [0..(newNode-1)] ++ concat cur --choose a node proportional to degree + A
    lastPA <- elements $ filter (`notElem`nonOptions) choices --choose a node that isn't connected already
    let newCur = addEdge cur newNode lastPA
    return (newCur, lastPA)

{-
Executes one TF step for the newest node.
Chooses randomly a non-neighbor node from the neighborhood of lastPA.
If not such neighbor exists, executes a PA step.

Input:
(current network, node that attached in last PA step)
att: initial attractiveness

Output:
(New network, node that attached in last PA step) --latter might have changed if no tfStep was possible
-}
tfStep :: ([[Int]], Int) -> Int -> Gen ([[Int]], Int)
tfStep (cur,lastPA) att = do
    let curNode = length cur -1
        nonOptions = curNode : (cur !! curNode) --nodes that are already attached aren't a valid choice, neither is the node itself
        choices = filter (`notElem` nonOptions) $ cur !! lastPA
    if null choices
        then paStep cur att
        else do
            triadNode <- elements choices
            let newCur = addEdge cur curNode triadNode
            return (newCur,lastPA)


{-
Adds an undirected edge from node v to w.
Assumes v and w are in the network!

Input:
current network
node v
node w

-}
addEdge:: [[Int]] -> Int -> Int -> [[Int]]
addEdge cur v w =  insertAt v w (insertAt w v cur)


{-
Inserts w into the neighborhood of v.

Input
Node v
Node w
network
-}
insertAt :: Int -> Int -> [[Int]] -> [[Int]]
insertAt _ _ []     = [] --shouldn't happen
insertAt 0 w (x:xs) | w `notElem` x = (w:x) : xs
                    | otherwise     = x:xs
insertAt v w (x:xs) = x : insertAt (v - 1) w xs



{-
Takes an adjacency list and translates it into a Relation (adjencecy set)
-}
translate :: [[Int]] -> Relation
translate xs = V.fromList $  L.map IntSet.fromList xs


{-- UNCOMMENT HERE

--takes current relation and the nr of agents to still be added
--add new nodes with preferential attachment
preferentialAttachment :: [[Int]] -> Int -> Gen [[Int]]
preferentialAttachment cur 0 = return $ reverse cur --here we can directly take care of reversing (and as in the beginning the core is symmetric, it shouldn't matter)
preferentialAttachment cur i = do
    let n = length cur --n is at the same time the name of the agent we are currently adding
        --TODO maybe store the in-degree in a counter, so I don't have to go through it every time?
        inDegreeAgs = (concatMap (replicate 2) [0..n]) ++ concat cur --makes sure all existing nodes show up at least once (including the new node itself (WHY does that make sense?)), and proportional to their in-degree
    thisAgsFriends <- sublistOfLength dBot dCap inDegreeAgs
    --inDegree <- sublistOfLength 0 dCap [0..n-1]  --TODO CONTINUE HERE optionally have some existing nodes attach to the new node, bc the average in-degree of public nodes is ridiculosly low. note that these will not be the final names of the agents, bc the intermediate list is reversed
    preferentialAttachment (thisAgsFriends : cur) (i-1) --ACHTUNG like this we have to reverse the final thing, but we save time



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


{-
Input:
lmin: Lower limit of desired length of output
lmax: Upper limit of desired length of output
xs: list

Output:
a random subsequence of xs of random length between lmin and lmax
-}
sublistOfLength :: Ord a => Int -> Int -> [a] -> Gen [a]
sublistOfLength lmin lmax xs = do
    thisL <- chooseInt (lmin,lmax)
    sublistRec thisL xs

{-
Input:
l: desired length of output
xs: list

Output:
random subsequence of xs of length l
-}
sublistRec :: Eq a => Int -> [a] -> Gen [a]
sublistRec 0 _ = return []
sublistRec l xs = do
    if null xs then return [] --elements throws error if xs is empty
        else do el <- elements xs
                rest <- sublistRec (l-1) $ filter (/= el) xs --assuming we don't choose with replacement
                return $ el:rest


{-
Generates an arbitrary Holme-Kim Relation for each of the two topics.

TODO with same initialcore -> relevant? Wanted??
-}
constructRelMap :: Gen (M.Map Topic Relation, [Int])
constructRelMap = do
    climateRel <- holmeKim nParam mParam m0Param pTParam aParam
    relT2 <- holmeKim nParam mParam m0Param pTParam aParam
    let (_, elite') = findKrich eliteNrAgs climateRel
    return (M.fromList [(T 1, climateRel), (T 2, relT2)], elite')


--takes List of public, returns climate dual

--TODO adapt
--we assume that the positions are hierarchichal in the INITIAL model -> begründen, zudemwird das aber nachher nicht mehr angenommen (aber ergibt sich das???)

constructClimateDual :: [Int] -> Gen (IntMap (Set Position))
constructClimateDual public' = do
    takePolitical <- sublistRec nrPolitical public'
    takeNorm <- sublistRec nrNorm takePolitical
    takeIncome <- sublistRec nrIncome takeNorm
    let politicalMap = L.foldl' (\cur k -> IntMap.insert k p cur) IntMap.empty takePolitical
        normMap = L.foldl' (\cur k -> IntMap.insert k np cur) politicalMap takeNorm --value will be replaced for existing keys
    return $ L.foldl' (\cur k -> IntMap.insert k npi cur) normMap takeIncome

--take list of public
constructDualMap :: [Int] -> Gen (M.Map Topic (IntMap (Set Position)))
constructDualMap public' = do
    dualT2 <- randomDualT t2Positions allAgs ----TODO anpassen auf zahlen aus der lit
    dualClimate <- constructClimateDual public'
    return $ M.fromList [(T 1, dualClimate), (T 2, dualT2)]



{-TODO NEW IDEA-}

flight :: Topic
flight = T 3

ballot, flightNorm :: Position
ballot = P 5
flightNorm = P 6


ba, baf :: Set Position
ba = S.singleton ballot
baf = S.fromList [ballot, flightNorm]

propoBallot :: Double
propoBallot = 0.58

nrBallot :: Int
nrBallot = computeProportion propoBallot publicNrAgs

{-
(List of public, list of elite)
-}
constructFlightDual :: ([Int], [Int]) -> Gen (IntMap (Set Position))
constructFlightDual (public', elite') = do
    takeBallot <- sublistRec nrBallot public'
    return $ IntMap.fromList $ zip takeBallot (repeat ba) ++ zip elite' (repeat baf)

constructFlightRelMap :: Gen (M.Map Topic Relation, [Int])
constructFlightRelMap = do
    flightRel <- holmeKim nParam mParam m0Param pTParam aParam
    let (_, elite') = findKrich eliteNrAgs flightRel
    return (M.singleton flight flightRel, elite')



{-
Generate an arbitrary CaseSNM.
-}
instance Arbitrary CaseSNM where
  arbitrary = do
    (rel', elite') <- constructRelMap
    let public' = allAgs L.\\ elite'
    dual' <- constructDualMap public'
    return (CSNM (SNM totalNrAgs posMapCase rel' dual') elite') --elite will be ordered in ascening order of nr in-degree

{- would have been for comparison with random, but I'm not doing that
makeCSNMRandomRel :: Gen CaseSNM
makeCSNMRandomRel = do
    rel1 <- randomRel 120
    rel2 <- randomRel 120
    let (public', elite') = findKrich eliteNrAgs rel1
        rel' = M.fromList [(T 1, rel1), (T 2, rel2)]
    dual' <- constructDualMap public'
    return (CSNM (SNM totalNrAgs posMapCase rel' dual') elite')

    -}




{-
Input: Climate Dual, List of Elite
Returns: nr of agents from public holding each position (political, norm, income)
-}
majorityVotePub :: IntMap (Set Position) -> [Int] -> (Int, Int, Int)
majorityVotePub dual_t elite' = IntMap.foldlWithKey' increaseCounter (0,0,0) dual_t where
    increaseCounter count ag set | ag `notElem` elite' = S.foldl' increaseAccording count set
                                 | otherwise = count --only count the positions of the public
    increaseAccording (i, j, k) elem' | elem' == politicalPos = (i+1, j, k)
                                      | elem' == normPos = (i, j+1, k)
                                      | otherwise = (i, j, k+1)



--TODO test


{-
Input: Mode of Selec, Mode of Infl, CaseSNM
Returns: CaseSNM after interleaving of the two has stabilized, number of iterations until stabilization was reached
-}

runInterleaving :: Mode -> Mode -> CaseSNM -> (SNModel, Int)
runInterleaving Basic Basic (CSNM snm _) = fixCount (( updSelecBasic 0.5). (updInflBasic  threshold)) snm
runInterleaving Basic Variant (CSNM snm _) = fixCount (( updSelecBasic 0.5). (updInflVariant  threshold)) snm
runInterleaving Variant Basic (CSNM snm _) = fixCount (( updSelecVariant 0.5). (updInflBasic  threshold)) snm
runInterleaving Variant Variant (CSNM snm _) = fixCount (( updSelecVariant 0.5). (updInflVariant  threshold)) snm


{-
Input: mode of selection, mode of social influence, CaseSNM
Returns: runs experiment prints information
-}
runExperiment :: Mode -> Mode -> CaseSNM -> IO()
runExperiment selecMode inflMode m@(CSNM snm elite') = do
    let (initAvgOutPublic, initAvgInPublic, initAvgOutElite, initAvgInElite) = averageDegreesCSNModel m
        (finalModel, steps) = runInterleaving selecMode inflMode m
        finalClimateDual = (dual finalModel) M.! (T 1)
        (polNr, normNr, incomeNr) = majorityVotePub finalClimateDual elite'
        (finalAvgOutPublic, finalAvgInPublic, finalAvgOutElite, finalAvgInElite) = averageDegreesCSNModel (CSNM finalModel elite')
    putStr $ "You ran " ++ show selecMode ++ "Selec on " ++ show inflMode ++ "Infl. \n The starting Model has " ++ show eliteNrAgs ++ " Elite nodes and " ++ show publicNrAgs ++
                " Public nodes. \n Following initial average degrees: \n Average OutDegree Public: " ++ show initAvgOutPublic ++ "\n Average InDegree Public: " ++ show initAvgInPublic ++
                "\n Average OutDegree Elite: " ++ show initAvgOutElite ++ "\n Average InDegree Elite: " ++ show initAvgInElite ++ "\n The experiment stabilized after " ++
                show steps ++ " steps. \n Following final average degrees: \n Average OutDegree Public: " ++ show finalAvgOutPublic ++ "\n Average InDegree Public: " ++
                show finalAvgInPublic ++ "\n Average OutDegree Elite: " ++ show finalAvgOutElite++ "\n Average InDegree Elite: " ++ show finalAvgInElite ++
                "\n The majority vote in the final model is as follows. \n Public nodes holding political action: " ++ show polNr ++ "\n Public nodes holding social norm: " ++ show normNr ++
                "\n Public nodes holding income contribution: " ++ show incomeNr ++ "\n"




--HELPERS :)

--CaseSNM, returns (avgOutPublic, avgInPublic, avgOutElite, avgInElite)
averageDegreesCSNModel :: CaseSNM -> (Double, Double, Double, Double)
averageDegreesCSNModel (CSNM (SNM _ _ rel' _) elite') = averageDegrees (rel' M.! (T 1)) elite'

--Relation,  returns (avgOutPublic, avgInPublic, avgOutElite, avgInElite)
averageDegreesfromRel :: Relation -> (Double, Double, Double, Double)
averageDegreesfromRel rel' = averageDegrees rel' elite' where
    elite' = snd $ findKrich eliteNrAgs rel'

--Relation, list of elite, returns (avgOutPublic, avgInPublic, avgOutElite, avgInElite WITHIN the respective group)
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

generate (sublistRec 3 [1,2,3,4,5])
-}
--averageDegreesCSNModel <$> (generate arbitrary :: IO CaseSNM)