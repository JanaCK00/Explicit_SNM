{-# LANGUAGE TupleSections #-}
module CaseStudy where

import SNModel
    ( val_t,
      SNModel(SNM, rel, nrAgents, dualVal),
       valToDualVal_t)
import Test.QuickCheck
  (  Gen
  , elements, generate, choose)
import Test.QuickCheck.Gen (genDouble)
import GenerationUtils (sublistRec)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
import qualified Data.List as L
import Data.Ord (Down(..))
import Semantics

import Control.Monad (replicateM, forM) --for experiment
import Text.Printf --to print results of experiment
import Data.Maybe (isNothing)

import Syntax (Mode (Basic, Variant))
import Types


{-
This module implements the necessary code for the case study.
It includes:
 (1) an implementation of Holme-Kim network generation;
 (2) random generation of SNMs for the case study
 (3) running the experiment and printing the results to the console.
-}


--------------------------------------------------------------------------------
-- Definition of parameters
--------------------------------------------------------------------------------


{-
Define necessary Topics, Positions, Maps and Sets of Positions for the case study.
-}
sustainability :: Topic
sustainability = T 1

politicalNorm, financialNorm, lifestyleNorm :: Position
politicalNorm = P 1
financialNorm = P 2
lifestyleNorm = P 3


posMapSust :: M.Map Topic (Set Position)
posMapSust = M.singleton sustainability (S.fromList [politicalNorm, lifestyleNorm, financialNorm])


{-
Define proportion of distribution of position politicalNorm in initial network.
58% of nodes will hold position politicalNorm initially.
The number is taken from literature.
-}
propoBallot :: Double
propoBallot = 0.58

{-
Compute the absolute number of nodes who will hold the position politicalNorm initially, according to the proportion.
With propoBallot = 0.58 -> 70
-}
nrBallot :: Int
nrBallot = computeProportion propoBallot totalNrAgs

{-
Input:
0<=p<=1 proportion
n

Computes the integer number corresponding to a given proportion of a total (rounded to the nearest integer).
-}
computeProportion :: (RealFrac a, Integral b, Integral c) => a -> c -> b
computeProportion p n = round (p * fromIntegral n + 1e-9)



{-
Define fixed parameters for Holme-Kim network generation.
-}

totalNrAgs, m0Param, mParam, nParam, aParam  :: Int
threshold :: Double


totalNrAgs = 120    --number of agents in the generated networks
threshold = 0.5     --fixed threshold applied throughout the case study
nParam = totalNrAgs --number of nodes in generated network
mParam = 3          --number of edges added per node in network generation
m0Param = 3         --size of starting network in generation
aParam = 0          --initial attractiveness
--The average number of TF trials per added node is m_t = (m-1) * p_t. For m=3, this means m_t = 2 * p_t.



--------------------------------------------------------------------------------
-- Implementation of Holme Kim network generation
--------------------------------------------------------------------------------


{-
Constructs a fully connected network of a given size (no self-loops).
-}
initialCore :: Int -> [[Int]]
initialCore m_0 = initialCoreRec 0 where
    initialCoreRec  step | m_0 == step = []
                         | otherwise = filter (/= step) [0..(m_0-1)] : initialCoreRec (step + 1)



--TODO: write tests
--zb number of edges
--number of nodes
--auch gutes Zeichen: average degree macht sinn
--vlt auch noch clustering degree berechnen?x
--ist es symmetrisch?

{-
Generates a Holme-Kim relation
Input:
N:            number of nodes in final network
m:            number of edges added per new node
m ≤ m_0 < N : number of initial nodes
p_t :         probability of a triad formation (TF) step
A :           initial attractiveness for preferential attachment (PA)
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
Adds a symmetric edge from node v to w.
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
Assumes v is in the network!

Input
Node v
Node w
network
-}
insertAt :: Int -> Int -> [[Int]] -> [[Int]]
insertAt _ _ []     = [] --shouldn't happen, because we assume v is in the network
insertAt 0 w (x:xs) | w `notElem` x = (w:x) : xs
                    | otherwise     = x:xs
insertAt v w (x:xs) = x : insertAt (v - 1) w xs



{-
Takes a list of adjacency lists and translates it into a Relation (vector of adjacency sets)
-}
translate :: [[Int]] -> Relation
translate xs = V.fromList $  L.map IntSet.fromList xs



--------------------------------------------------------------------------------
-- Generation of SNMs for the case study
--------------------------------------------------------------------------------


{-
Define a wrapper type to allow arbitrary generation of SNMs that fulfill the defined
properties for the case study.

Additionally allows to store the majority opinion combination.
-}

data SNMCase = SNMCase
    { model :: SNModel
    , popularPos :: Set Position  --Stores the set of popular positions (>50% of agents hold it).
    } deriving (Eq, Show)


{-
TODO delete if unnecessary, used for testing
unwraps the newtype SNMCase
-}
unwrap :: SNMCase -> SNModel
unwrap (SNMCase snm _) = snm


{-
Generates an SNMCase with arbitrary Holme-Kim Relation,
and randomly distributed position politicalNorm according to the proportion.

p_t: parameter for holme kim (clustering)
-}


randomSNMCase :: Double -> Gen SNMCase
randomSNMCase p_t = do
        --Generate a random Holme-Kim relation.
        sustainabilityRel <- holmeKim nParam mParam m0Param p_t aParam
        let rel' = M.singleton sustainability sustainabilityRel
            ags = [0..totalNrAgs-1]
        --Randomly pick the agents who hold the position "politicalNorm".
        takeBallot <- IntSet.fromList <$> sublistRec nrBallot ags --TODO have this be random as well
        --Randomly pick the agents who will hold position TODO.
        nrMoneyNorm <- choose (0,totalNrAgs) --TODO have this be a parameter as well?
        takeMoneyNorm <- IntSet.fromList <$> sublistRec nrMoneyNorm ags
        --Build the set of popular positions.
        let popular | nrMoneyNorm * 2 > totalNrAgs = S.fromList [politicalNorm, financialNorm]
                    | otherwise                    = S.singleton politicalNorm
        --Assign the valuation.
        let val_t' = M.fromList [(politicalNorm, takeBallot), (financialNorm, takeMoneyNorm)]
        let dualVal' = M.singleton sustainability $ valToDualVal_t val_t'
        --Return the SNM and the popular positions.
        return $ SNMCase (SNM totalNrAgs posMapSust rel' dualVal') popular


{-
Example usage in ghci:
import Test.QuickCheck
generate $ randomSNMCase 0.5
-}



--------------------------------------------------------------------------------
-- Running the experiment
--------------------------------------------------------------------------------

{-
Defining the parameters.
-}

--The values for the parameter p_t in Holme Kim.
ourPts :: [Double]
ourPts = [0, 0.5, 0.8]

--The values for the number of leaders picked.
ourKs :: [Int]
ourKs = [15, 20, 25, 30]

{-
Data type for the intervention strategy.
Popular: opinion leaders adapt their positions to mirror the popular stances.
Authentic: opinion leaders stick to their positions
-}

data InterventionStrat = Popular | Authentic deriving (Show, Eq, Ord)


{-
Number of agents -> 120
parameters of holme kim -> as defined above
Threshold -> 0.5
InflMode -> Basic
SelecMode -> Basic -> easier to justify

Input:
p_t: current paramter for holme kim
n: Number of models to generate
ks: list of values for k to test

Will generate n SNMCase using the parameter p_t for Holme Kim.
Will then test each value for k for each intervention strategy on each of the n relations.
Returns average results over the runs.
-}
experimentHolme :: Double -> Int -> [Int] -> Gen [(Int, InterventionStrat, Results)]
experimentHolme p_t n ks = do
    caseModels <- replicateM n (randomSNMCase p_t)
    allResults <- forM caseModels $ \rel' ->
        forM ks $ \k ->
            forM [Popular, Authentic] $ \interventionStrat -> do
                resultOne <- runOneGen interventionStrat k rel'
                pure (k, interventionStrat, resultOne)
    return $ aggregate ks (concat $ concat allResults)


{-
Input:
List of values for k
List of experiment results inlcuding k and Strategy.

Output:
Aggregates the results by k and Strategy, to display average values across the generated models.
-}
aggregate :: [Int]  -> [(Int, InterventionStrat, Results)] -> [(Int, InterventionStrat, Results)]
aggregate ks listOfResults =
    [ (k, s, averageResult [x | (k', s', x) <- listOfResults, k == k', s == s'])
    | k <- ks
    , s <- [Popular, Authentic]
    ]

{-
Input:
Assumes non-empty list as input.
List of experiment Results (single runs).

Output:
Calculates average of Results.

-}
averageResult :: [Results] -> Results
averageResult xs = addedUp `divideInt` length xs where
    addedUp = sumResults xs
    divideInt (Results p l s r adop rejec partialSucc) i = Results (fI p i) (fI l i) (fIM s i) (M.map (`fI` i) r) (fI adop i) (fI rejec i) (fI partialSucc i) where
        fI x y = x / fromIntegral y
        fIM Nothing _ = Nothing
        fIM (Just x) y = Just (x / fromIntegral y)

{-
Input: List of Results
Output: implements sum for [Results]
-}
sumResults :: [Results] -> Results
sumResults = L.foldl' addResults zeroResults where
    zeroResults = Results 0 0 (Just 0) M.empty 0 0 0
    addResults (Results a1 b1 c1 d1 e1 f1 g1) (Results a2 b2 c2 d2 e2 f2 g2) = Results (a1+a2) (b1+b2) ((+) <$> c1 <*> c2) (M.unionWith (+) d1 d2) (e1+e2) (f1+f2) (g1+g2)

{-
Data type to store results of experiment. Usually a single run of experiment, but can also be used to store an average.
TODO can be extended if necessary
-}
data Results = Results
    { avgPublic     :: Double                --Initial average degree of non-leader nodes
    , avgLeaders    :: Double                --Initial average degree of leader nodes
    , stab          :: Maybe Double          --Number of iteration until stabilization. Nothing if none was reached.
    , adoptRatios   :: M.Map Position Double --Ratio of nodes who hold each position in the final model.
    , fullyAdopted  :: Double                --Number of times all agents adopted the new position in the final model.
    , fullyRejected :: Double                --Number of times no agents adopted the new position in the final model.
    , partialSuccess :: Double               --Number of times more than 50% of all agents adopted the new position in the final model.
    } deriving (Show)

{-
Input:
Leader Identification Strategy
0 < k <= totalNrAgs: number of leaders
SNMCase

Output:
Identifies k leaders according to strategy, runs the experiment and return the results.

-}
runOneGen :: InterventionStrat -> Int -> SNMCase -> Gen Results
runOneGen popStrat k snmCase = do
    let snm = model snmCase
    leaders <- getLeaders KRich k (rel snm M.! sustainability)
    return $ runOne popStrat leaders snmCase



{-
Input:
Popularty Strategy
List of leaders (0 < length <= nr of Agents)
SNMCase

Output:
Intervenes on positions of leaders, runs interleaving and returns results.
-}
runOne :: InterventionStrat -> [Int] -> SNMCase -> Results
runOne popStrat leaders snmCase   = Results avgPublic' avgLeaders' stab' finalDistribution fullyA fullyR partSucc where
    snm                       = model snmCase
    pops                      = popularPos snmCase
    interveneSNM              = snm {dualVal = M.singleton sustainability (intervention popStrat pops leaders dualVal_sustainability)}
    (avgPublic', avgLeaders') = averageDegrees sustainabilityRel leaders
    (finalModel , stab'')     = interleave Basic Basic threshold interveneSNM --TODO either Basic on Basic or Variant on Variant
    finalDistribution         = posDistribution_t finalModel sustainability
    sustainabilityRel                 = rel snm M.! sustainability
    stab'                     = fromIntegral <$> stab''
    dualVal_sustainability            = dualVal snm M.! sustainability
    (fullyA, fullyR, partSucc)| isNothing (M.lookup lifestyleNorm finalDistribution) = (0.0, 1.0, 0.0)
                              | finalDistribution M.! lifestyleNorm  == 1.0          = (1.0, 0.0, 0.0)
                              | finalDistribution M.! lifestyleNorm > 0.5            = (0.0, 0.0, 1.0) --only bigger than 0.5 but smaller than 1.0
                              | otherwise                                         = (0, 0, 0)       -- <= 0.5 and >0




{-
Input:
Popularity Strategy
Set of popular positions
List of leaders
DualVal_t: DualVal of a specific topic

Output: New dualVal_t where the leaders have their new positions after intervention.
-}
intervention :: InterventionStrat -> Set Position -> [Int] -> IntMap (Set Position) -> IntMap (Set Position)
intervention Authentic _ leaders dualVal_t = IntMap.unionWith S.union dualVal_t $ IntMap.fromList $ map (, S.singleton lifestyleNorm) leaders --insert lifestyleNorm for all leaders
intervention Popular pops leaders dualVal_t = IntMap.union (IntMap.fromList $ map (, S.insert lifestyleNorm pops) leaders) dualVal_t

{-
Input:
p_t: Parameter for Holme Kim
n > 0: Number of models to generat
List of values for k to test

Output:
Runs experiment and prints results.
-}
runAndShow :: Double -> Int -> [Int] -> IO()
runAndShow p_t n ks = do
    putStr $ "WELCOME to the experiment zone :) In your experiment, " ++ show n ++ " Holme-Kim networks with p_t = " ++ show p_t ++ " and "++ show totalNrAgs ++
        " nodes were randomly generated. \n The tested values for the number of leaders were: " ++ show ks ++
        ". Are you READY for the results? \n"
    results <- generate (experimentHolme p_t n ks)
    printTable results



{-
Input: A list of aggregated result.
Output: Prints the results to the console.
-}

printTable :: [(Int, InterventionStrat, Results)] -> IO()
printTable results = do
    let strategyMap = M.fromListWith (++) [ (s, [(k, r)]) | (k, s, r) <- results]
    printPopStrategy Popular (strategyMap M.! Popular)
    printPopStrategy Authentic (strategyMap M.! Authentic)



--Print to console
printPopStrategy :: InterventionStrat -> [(Int, Results)] -> IO ()
printPopStrategy s xs = do
    putStrLn $ "\n=== " ++ show s ++ " ==="
    printf "%5s %10s %10s %10s %10s %10s %10s %10s\n"
        "k" "Degree Public" "Degree Leaders" "Rounds" "Ratio" "Success" "Failure" "Partial"
    mapM_ printRow xs
  where
    printRow (k, Results a' b' c' d' e' f' g') =
        printf "%5d %10.3f %10.3f %10s %10s %10s %10s %10s\n"
            k a' b' (show c') (show d') (show (e'*100) ++ "%") (show (f'*100) ++ "%") (show (g'*100) ++ "%")

--usage in ghci:
{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel

generate (sublistRec 3 [1,2,3,4,5])
-}
--averageDegreesCSNModel <$> (generate arbitrary :: IO CaseSNM)


--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

{-
Input: SNmodel, Topic
Output: Returns a list of tuples. Each tuple says which fraction of agents in the network hold that position.
Positions that aren't held by any node don't appear in the result.
The output list will be sorted in ascending order of Position (M.toList returs it this way).
-}
posDistribution_t :: SNModel -> Topic  -> M.Map Position Double
posDistribution_t snm t =  M.map (\s -> fromIntegral (IntSet.size s) / fromIntegral nrAgs) val_t' where
    val_t' = val_t snm t
    nrAgs = nrAgents snm --assume >0

--TODO test




{-
Input:
Relation
List of leaders, length > 0

Output:
Tuple of (average degree of non-leader node, average degree of leader node)
-}
averageDegrees :: Relation -> [Int] -> (Double, Double)
averageDegrees rel' leaders'= (avgPublic', avgLeaders') where
    degrees = V.map IntSet.size rel'
    sumDegrees = sum degrees
    leadersDegree = V.ifoldl' (\acc i x ->
        if IntSet.member i leadersSet
            then acc + x
            else acc) 0 degrees
    publicDegree = sumDegrees - leadersDegree
    leadersSet = IntSet.fromList leaders'
    nrleaders = length leaders'
    nrPublic = V.length rel' - nrleaders
    avgPublic' | nrPublic == 0 = 0
               | otherwise     = fromIntegral publicDegree / fromIntegral nrPublic
    avgLeaders' = fromIntegral leadersDegree / fromIntegral nrleaders




{-
Data type for the identification strategies for leaders:

KRich: Highest degree nodes in the network. -> opinion leaders
Random: Randomly chosen nodes.              -> volunteers
-}
data Strategy = Random | KRich deriving (Show, Eq, Ord) --TODO will probably not use Random, might just show that the average degree is way lower

{-
Input:
Leader identification strategy
Number of Leaders to identify
Relation

Output:
List of leaders

--TODO test all helper functions, and this one
-}
getLeaders :: Strategy -> Int -> Relation -> Gen [Int]
getLeaders KRich nrLeaders rel' = return $ findKrich nrLeaders rel'
getLeaders Random nrLeaders rel' = do
    sublistRec nrLeaders [0..V.length rel'-1]

{-
Input
k: number of leaders to identify
Relation

Output:
Tuple of (List of non-leaders, List of leaders)

TODO maybe I have to change this?
(For a tie, there is no defined rule.)

TODO test
-}

findKrich :: Int -> Relation -> [Int]
findKrich k rel' = take k $ map fst $ degreeListDesc rel'

{-
Input: Relation
Output: a list of tuples (agent, number of friends),
    sorted on descending number of friends

TODO test
-}
degreeListDesc :: Relation -> [(Int, Int)]
degreeListDesc = L.sortOn (Down . snd) . V.toList . V.imap (\i ags -> (i, IntSet.size ags))