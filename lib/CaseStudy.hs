module CaseStudy where

import SNModel
    ( val_t,
      Position(..),
      SNModel(SNM, rel, nrAgents, dualVal),
      Topic(..), valToDual_t)
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , elements, generate, sublistOf, chooseInt)
import Test.QuickCheck.Gen (genDouble)
import SetTheory (Agent, Relation, sublistRec)
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
import Debug.Trace (trace)
import Data.Maybe (isNothing)

import Syntax (Mode (Basic, Variant))


{-
Input:
maxIter: maximum number of iterations
f: function (endomorphism)

Output:
Returns the function that will apply f until the output is stable or the maximum number of iterations has been reached.
Then it will return a tuple of (stabilized output, number of iterations it took until stable).
If stabilization wasn't reached in maxIter rounds, Nothing is returned for the number of iterations.
-}
stabCountSafe :: Eq a => Int -> (a -> a) -> a -> (a, Maybe Int)
stabCountSafe maxIter f = go 0 where
    go k current | k >= maxIter  = (current, Nothing)
                 | x' == current = (current, Just k)
                 | otherwise     = go (k + 1) x'
      where
        x' = f current

{-
Define necessary Topics, Positions, Maps and Sets of Positions for the case study.
-}
flight :: Topic
flight = T 3

ballot, flightNorm, thirdOne, fourthOne :: Position
ballot = P 5
flightNorm = P 6
thirdOne = P 7
fourthOne = P 8

posMapFlight :: M.Map Topic (Set Position)
posMapFlight = M.singleton flight (S.fromList [ballot, flightNorm, thirdOne])


{-
Define proportion of distribution of position ballot in initial network.
58% percent of nodes will hold position ballot initially.
The number is taken from literature.
-}
propoBallot :: Double
propoBallot = 0.58 --TODO have this as a variable

{-
Compute the absolute number of nodes who will hold the position ballot initially, according to the proportion.
-}
nrBallot :: Int
nrBallot = computeProportion propoBallot totalNrAgs

{-
Input:
0<=p<=1 proportion
n

Computes the integer number corresponding to a given proportion of a total (rounded down).
-}
computeProportion :: (RealFrac a, Integral b, Integral c) => a -> c -> b
computeProportion p n = floor (p * fromIntegral n + 1e-9)

--define necessary parameters
--CHANGE if needed
totalNrAgs, m0Param, mParam, nParam, aParam  :: Int
threshold, pTParam :: Double


totalNrAgs = 120    --number of agents in the generated networks
threshold = 0.5     --fixed threshold applied throughout the case study

{-
Define fixed parameters for Holme-Kim network generation.
-}
nParam = totalNrAgs --number of nodes in generated network
mParam = 3          --number of edges added per node in network generation
m0Param = 3         --size of starting network in generation
pTParam = 0.5       --probability of a TF step.
aParam = 1          --initial attractiveness
--The average number of TF trials per added node is m_t = (m-1) * p_t. For m=3, this means m_t = 2 * p_t.

--TODO find good starting value
--decides the number of randomly chosen starting nodes for nomination strategy
indexSize :: Int
indexSize = 10




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
Takes an adjacency list and translates it into a Relation (adjacency set)
-}
translate :: [[Int]] -> Relation
translate xs = V.fromList $  L.map IntSet.fromList xs


{-
Define a wrapper type to allow arbitrary generation of SNMs that fulfill the defined
properties for the case study.

Additionally allows to store the majority opinion combination.
-}

data SNMCase = SNMCase
    { model :: SNModel
    , popularPos :: Set Position  --stores the popular opinion combination
    } deriving (Eq, Show)


{-
TODO delete if unnecessary, used for testing
unwraps the newtype SNMCase
-}
unwrap :: SNMCase -> SNModel
unwrap (SNMCase snm _) = snm


{-
Generates an SNMCase with arbitrary Holme-Kim Relation,
and randomly distributed position ballot according to the proportion.
-}
instance Arbitrary SNMCase where
    arbitrary = do
        flightRel <- holmeKim nParam mParam m0Param pTParam aParam
        let rel' = M.singleton flight flightRel
            ags = [0..totalNrAgs-1]
        takeBallot <- IntSet.fromList <$> sublistRec 60 ags
        takeThirdOne <- IntSet.fromList <$> sublistRec 120 ags --TODO tweaking here
        --takeFourthOne <- IntSet.fromList <$> sublistRec 70 ags
        let popular = S.empty--TODO continue here to get out the majority
        let val_t' = M.fromList [(ballot, takeBallot), (thirdOne, takeThirdOne)]
        let dualVal' = M.singleton flight $ valToDual_t val_t'
        return $ SNMCase (SNM totalNrAgs posMapFlight rel' dualVal') popular


getSNMCase :: Gen SNMCase
getSNMCase = arbitrary



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
Mode of Selec
Mode of Infl
SNM

Output:
SNM after stabilization of the interleaving
Number of iterations until stabilization
If no stabilization was reached after 20 steps, Nothing is returned instead of the number.
-}
interleave :: Mode -> Mode -> SNModel -> (SNModel, Maybe Int)
interleave Basic Basic      = stabCountSafe 20 (updSelecBasic threshold . updInflBasic threshold)
interleave Basic Variant    = stabCountSafe 20 (updSelecBasic threshold . updInflVariant threshold)
interleave Variant Basic    = stabCountSafe 20 (updSelecVariant threshold . updInflBasic threshold)
interleave Variant Variant  = stabCountSafe 20 (updSelecVariant threshold . updInflVariant threshold)


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

KRich: Highest degree nodes in the network. Corresponds to celebrity strategy. OR the full mapping?
Random: Randomly chosen nodes. Corresponds to volunteer strategy.
Nomination: Randomly choose nodes, which then recommend the highest degree node in their neighboorhood.(global knowledge) Corresponds to snowball strategy.
LocalNom: All nodes recommend their most locally embedded node, then we choose the most nominated ones --TODO keep working on these, also have it with smaller sample size, and for the case that we don't find enough on level 1
-}
data Strategy = Random | KRich deriving (Show, Eq, Ord) --UNCOMMENT HERE for the identification strategies: | Nomination | LocalNom


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



{-
TODO working on new idea

Popular: opinion leaders take up the popular existing norm
Authentic: opinion leaders stick to their initial stance in the existinc norm
-}

data PopularStrat = Popular | Authentic deriving (Show, Eq, Ord)


{-
have a list of all the varying parameters


Number of agents -> 120
parameters of holme kim -> as defined above
Threshold -> 0.5
InflMode -> Basic
SelecMode -> Basic?

Input:
n: Number of models to generate
ks: list of k's to test

will generate the models, then generate the leaders using the three strategies
will save for each k the percentage of successes in each of the three strategies
(KRich, Random, Nomination)


ACHTUNG ._.
-}
experimentHolme :: Int -> [Int] -> Gen [(Int, PopularStrat, Results)]
experimentHolme n ks = do
    caseModels <- replicateM n getSNMCase
    let models = map unwrap caseModels --TODO here das einbauchen mit der popular opinion combo
    allResults <- forM models $ \rel' ->
        forM ks $ \k ->
            forM [Popular, Authentic] $ \popularStrat -> do --todo habe hier Nomination und LocalNom rausgenommen
                resultOne <- runOneGen popularStrat k rel'
                pure (k, popularStrat, resultOne)
    return $ aggregate ks (concat $ concat allResults)


{-
Input:
List of values for k
List of experiment results inlcuding k and Strategy.

Output:
Aggregates the results by k and Strategy, to display average values across the generated models.
-}
aggregate :: [Int]  -> [(Int, PopularStrat, Results)] -> [(Int, PopularStrat, Results)]
aggregate ks listOfResults =
    [ (k, s, averageResult [x | (k', s', x) <- listOfResults, k == k', s == s'])
    | k <- ks
    , s <- [Popular, Authentic]--TODO habe hier Nomination und LocalNom rausgenommen
    ]

{-
Input:
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
    zeroResults = Results 0 0 (Just 0) M.empty 0 0 0--TODO check if it works with [] as last argument, sonst rausholen
    addResults (Results a1 b1 c1 d1 e1 f1 g1) (Results a2 b2 c2 d2 e2 f2 g2) = Results (a1+a2) (b1+b2) ((+) <$> c1 <*> c2) (M.unionWith (+) d1 d2) (e1+e2) (f1+f2) (g1+g2)

{-
Data type to store results of experiment. Usually a single run of experiment, but can also be used to store an average.
TODO can be extended if necessary
-}
data Results = Results
    { avgPublic     :: Double                --Initial average degree of non-leader nodes
    , avgLeaders    :: Double                --Initial average degree of leader nodes
    , stab          :: Maybe Double          --Number of iteration until stabilization. Nothing if none was reached.
    , adoptRatios   :: M.Map Position Double --Ratio of nodes who hold each position.
    , fullyAdopted  :: Double                --Number of times all agents adopted the new position in the final model.
    , fullyRejected :: Double                 --Number of times no agents adopted the new position in the final model.
    , partialSuccess :: Double               --Number of times more than 50% of all agents adopted the new position in the final model (--TODO gute Zahl hier finden)
    } deriving (Show)

{-
Input:
Leader Identification Strategy
0 < k <= totalNrAgs: number of leaders
SNMCase

Output:
Identifies k leaders according to strategy, runs the experiment and return the results.

-}
runOneGen :: PopularStrat -> Int -> SNModel -> Gen Results
runOneGen popStrat k snm = do
    leaders <- getLeaders KRich k (rel snm M.! flight) --TODO habe hier KRich statt der Input Strategie reingetan
    return $ runOne popStrat leaders snm



{-
Input:
Popularty Strategy
List of leaders (0 < length <= nr of Agents)
SNMCase

Output:
Intervenes on positions of leaders, runs interleaving and returns results.
-}
runOne :: PopularStrat -> [Int] -> SNModel -> Results
runOne popStrat leaders snm   = Results avgPublic' avgLeaders' stab' finalDistribution fullyA fullyR partSucc where
    interveneSNM              = snm {dualVal = M.singleton flight (intervention popStrat leaders dualVal_flight)}
    (avgPublic', avgLeaders') = averageDegrees flightRel leaders
    (finalModel , stab'')     = interleave Variant Basic interveneSNM
    finalDistribution         = posDistribution_t finalModel flight
    flightRel                 = rel snm M.! flight
    stab'                     = fromIntegral <$> stab''
    dualVal_flight               = dualVal snm M.! flight
    (fullyA, fullyR, partSucc)| isNothing (M.lookup flightNorm finalDistribution) = (0.0, 1.0, 0.0)
                              | finalDistribution M.! flightNorm  == 1.0          = (1.0, 0.0, 1.0)
                              | finalDistribution M.! flightNorm > 0.5          = (0.0, 0.0, 1.0)
                              | otherwise                                         = (0, 0, 0)




{-
Input:
Popularity Strategy
List of leaders
Dual_t: Dual of a specific topic

Output: New dualVal_t where the leaders have their new positions after intervention.
-}
intervention :: PopularStrat -> [Int] -> IntMap (Set Position) -> IntMap (Set Position)
intervention Authentic leaders dualVal_t = IntMap.unionWith S.union dualVal_t $ IntMap.fromList $ zip leaders (repeat $ S.singleton flightNorm) --insert flightnorm for all leaders
intervention Popular leaders dualVal_t = IntMap.mapWithKey (\k v -> if isLeader k then S.fromList [flightNorm, thirdOne, ballot] else v) dualVal_t where
    isLeader k' = elem k' leaders -- TODO replace it for all leaders with the popular thing + flightnorm IntMap.unionWith S.union dualVal_t $ IntMap.fromList $ zip leaders (repeat $ S.fromList [flightNorm, thirdOne]) --I GET IT!!!! I have to remove them looooolll!! todo habe hier thirdOne und Ballot rausgenommen, als test wenn es nicht der mehrheit entspricht

{-
Input:
n > 0: Number of models to generat
List of values for k to test

Output:
Runs experiment and prints results.
-}
runAndShow :: Int -> [Int] -> IO()
runAndShow n ks = do
    putStr $ "WELCOME to the experiment zone :) In your experiment, " ++ show n ++ " Holme-Kim networks with " ++ show totalNrAgs ++
        " nodes were randomly generated. \n The tested values for the number of leaders were: " ++ show ks ++
        ". Are you READY for the results? \n"
    results <- generate (experimentHolme n ks)
    printTable results



{-
Input: A list of aggregated result.
Output: Prints the results to the console.
-}

printTable :: [(Int, PopularStrat, Results)] -> IO()
printTable results = do
    let strategyMap = M.fromListWith (++) [ (s, [(k, r)]) | (k, s, r) <- results]
    printPopStrategy Popular (strategyMap M.! Popular)
    printPopStrategy Authentic (strategyMap M.! Authentic)
    --printStrategy Nomination (strategyMap M.! Nomination) --TODO habe hier Nomination rausgenommen
    --printStrategy LocalNom (strategyMap M.! LocalNom)


--ACHTUNG . - .
--TODO xs is ordered the wrong way (decreasing)
printPopStrategy :: PopularStrat -> [(Int, Results)] -> IO ()
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