module CaseStudy where

import SNModel
    ( stabCountSafe,
      val_t,
      Position(..),
      SNModel(SNM, rel, nrAgents, dual),
      Topic(..) )
import Test.QuickCheck
  ( Arbitrary (..)
  , Gen
  , elements, generate)
import Test.QuickCheck.Gen (genDouble)
import SetTheory (Agent, Relation)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.IntSet as IntSet
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as M
import qualified Data.Vector as V
--import qualified Data.Vector.Mutable as MV
import qualified Data.List as L
import Data.Ord (Down(..))
import Data.Tuple (swap)
import Semantics

import Control.Monad (replicateM, forM) --for experiment
import Text.Printf --to print results of experiment

import Syntax (Mode (Basic, Variant))



newtype SNMCase = SNMCase SNModel deriving (Eq, Show)

--Question: do it with quickcheck, combine all test parameters into one counting thing to have it run on the same test cases
--genereate model, run until stable (if not stable after fixed nr of turn, stop), check proportion of public who hold climate positions

{-
Define necessary Topics, Positions, Maps and Sets of Positions for the case study.
-}
flight :: Topic
flight = T 3

ballot, flightNorm :: Position
ballot = P 5
flightNorm = P 6

posMapFlight :: M.Map Topic (Set Position)
posMapFlight = M.singleton flight (S.fromList [ballot, flightNorm])

ba, baf :: Set Position
ba = S.singleton ballot
baf = S.fromList [ballot, flightNorm]


{-
Define proportion of distribution of position ballot in initial network.
58% percent of nodes will hold position ballot initially.
-}
propoBallot :: Double
propoBallot = 0.58

{-
Compute the absolute number of nodes who will hold the position ballot initially, according to the proportion.
-}
nrBallot :: Int
nrBallot = computeProportion propoBallot totalNrAgs

{-
Computes the integer number corresponding to a given proportion of a total (rounded down)
-}
computeProportion :: (RealFrac a1, Integral b, Integral a2) => a1 -> a2 -> b
computeProportion propo ags = floor (propo * fromIntegral ags)

--define necessary parameters
--CHANGE if needed
publicNrAgs, leadersNrAgs, totalNrAgs, m0Param, mParam, nParam, aParam  :: Int
threshold, pTParam :: Double
--Define fixed parameters
totalNrAgs = 120    --number of agents in the generated networks
leadersNrAgs = 20     --TODO incoporate as a variable -> whereever it shows up, replace it with a parameter
publicNrAgs = totalNrAgs - leadersNrAgs --TODO incorporate as a variable
threshold = 0.5

{-
Fixed parameters for network generation (Holme-Kim)
-}
nParam = totalNrAgs --number of nodes in final network generated
mParam = 3          --number of edges added per node in network generation
m0Param = 3         --size of starting network in generation
pTParam = 0.8       --probability of a TF step
aParam = 1          --initial attractiveness

--TODO find good starting value
--decides the number of randomly chosen starting nodes for nomination strategy
indexSize :: Int
indexSize = 10

allAgs :: [Agent]
allAgs = [0..totalNrAgs-1]



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
Takes an adjacency list and translates it into a Relation (adjencecy set)
-}
translate :: [[Int]] -> Relation
translate xs = V.fromList $  L.map IntSet.fromList xs



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
Generates an SNMCase with arbitrary Holme-Kim Relation,
and randomly distributed position ballot according to the proportion.
-}
instance Arbitrary SNMCase where
    arbitrary = do
        flightRel <- holmeKim nParam mParam m0Param pTParam aParam
        let rel' = M.singleton flight flightRel
        takeBallot <- sublistRec nrBallot allAgs
        let dual' = M.singleton flight $ IntMap.fromList $ zip takeBallot (repeat ba)
        return $ SNMCase (SNM totalNrAgs posMapFlight rel' dual')


getSNMCase :: Gen SNMCase
getSNMCase = arbitrary

{-
Input: SNmodel, Topic
Output: Returns a list of tuples. Each tuple says which fraction of agents in the network hold that position.
Positions that aren't held by any node don't appear in the result.
The output list will be sorted in ascending order of Position (M.toList return it this way).
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
NEW EXPERIMENT
-}

runExperiment :: Mode -> Mode -> SNMCase -> [Int] -> IO()
runExperiment selecMode inflMode (SNMCase snm) leaders' = do
    let (initAvgPublic, initAvgleaders) = averageDegrees (rel snm M.! flight) leaders'
        (finalModel, steps) = interleave selecMode inflMode snm
        posDis = posDistribution_t finalModel flight
        (finalAvgPublic, finalAvgleaders) = averageDegrees (rel finalModel M.! flight) leaders'
    putStr $ "You ran " ++ show selecMode ++ "Selec on " ++ show inflMode ++ "Infl. \n The starting Model has " ++ show leadersNrAgs ++ " leader nodes and " ++ show publicNrAgs ++
                " Public nodes. \n Following initial average degrees: \n Average Degree of Public nodes: " ++ show initAvgPublic ++
                "\n Average Degree leader Nodes: " ++ show initAvgleaders  ++ "\n The experiment stabilized after " ++
                show steps ++ " steps. \n Following final average degrees: \n Average Degree Public nodes: " ++ show finalAvgPublic ++
                "\n Average Degree leaders nodes: " ++ show finalAvgleaders++
                "\n The positions distribution in the final model is as follows. " ++ show posDis ++ "\n"


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




--TODO keep working here



{-
Data type for the three identification strategy for leaders:

KRich: Highest degree nodes in the network. Corresponds to celebrity strategy.
Random: Randomly chosen nodes. Corresponds to volunteer strategy.
Reco: Randomly chose nodes, which then recommend the highest degree node in their neighboorhood. Corresponds to snowball strategy.
-}
data Strategy = Random | KRich | Nomination deriving (Show, Eq, Ord)


{-
Input:
Leader strategyification strategy
Number of Leaders
Relation

Output:
Generated tuple of (List of non-leaders, List of Leaders) --TODO vlt brauche ich die non-leaders gar nicht

--TODO test all helper functions, and this one
-}
getLeaders :: Strategy -> Int -> Relation -> Gen ([Int], [Int])
getLeaders KRich nrLeaders rel' = return $ findKrich nrLeaders rel'
getLeaders Random nrLeaders rel' = do
    let ags = [0..V.length rel'-1]
    leaders <- sublistRec nrLeaders ags
    let nonLeaders = IntSet.toList $ IntSet.difference (IntSet.fromList ags) (IntSet.fromList leaders)
    return (nonLeaders, leaders)
getLeaders Nomination nrLeaders rel' = do
    let agsSet = IntSet.fromList [0..V.length rel'-1]
    leaders <- nomination nrLeaders indexSize rel'
    let nonLeaders = IntSet.toList $ IntSet.difference agsSet (IntSet.fromList leaders)
    return (nonLeaders, leaders)



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

findKrich :: Int -> Relation -> ([Int], [Int])
findKrich k rel' = swap $ splitAt k $ map fst $ degreeListDesc rel'


{-
Input: Relation
Output: a list of tuples (agent, number of friends),
    sorted on descending number of friends

TODO test
-}
degreeListDesc :: Relation -> [(Int, Int)]
degreeListDesc = L.sortOn (Down . snd) . V.toList . V.imap (\i ags -> (i, IntSet.size ags))


--TODO debug: the level thing doesn't guaruantee we find all nodes as nominees -> fix this
{-
Input:
l: Level of nomination:
    for l=1, each agents nominates the highest degree node
    for l=2, each agents nominates the second highest degree node
    ...

List of nominators (agents who nominate)
Relation
Precomputed degreeList corresponding to the relation

Output:
IntMap showing for an entry (v, n), that the node v was nominated n times.

-}
getNomiMap :: Int -> [Int]  -> Relation -> [(Int, Int)] -> IntMap Int
getNomiMap _ [] _ _ = IntMap.empty
getNomiMap l (x:ags) rel' degrees | nrFriends >= l = IntMap.insertWith (+) nomi 1 rest
                                  | otherwise    = rest --if agent doesn't have anymore friends to nominate at level l
 where rest = getNomiMap l ags rel' degrees
       friends = rel' V.! x
       nrFriends = IntSet.size friends
       nomi = fst $ filter ((`IntSet.member` friends) . fst) degrees !! (l-1) --get nomination of agent a at level l




{-
Input:
Number of leaders to identify (<= number of agents in the network)
Size of index set (<= number of agents in the network)
Relation

Output:
Generated leaders using nomination strategy.
-}
nomination :: Int -> Int -> Relation -> Gen [Int]
nomination n i rel' = do
    let ags = [0..(V.length rel' - 1)]
    indexCases <- sublistRec i ags
    let degrees = degreeListDesc  rel'
    return $ nomiRec n rel' indexCases indexCases indexCases IntMap.empty degrees 1


{-
Input:
number of leaders to identify
Relation
list of indexset (original nominators)
list of current nominators
running list of nominators
running nomination map (keys are agents, value is number of times they have been nominated)
Precomputed degreeList corresponding to the relation
level of nomination

Output:
final list of leaders
-}
nomiRec ::  Int -> Relation -> [Int] -> [Int] -> [Int] -> IntMap Int -> [(Int, Int)] -> Int -> [Int]
nomiRec n rel' indexCases curNom nom nomMap degrees l | enough    = take n $ map fst $ L.sortOn (Down . snd) $ IntMap.toList newNomMap --if enough nominees have been found, take the n most nominated ones
                                                      | lfull     = nomiRec n rel' indexCases newNom [] newNomMap degrees (l+1)  --if all agents have already proveded a nomination, we increase the level of nomination
                                                      | otherwise = nomiRec n rel' indexCases newCurNom newNom newNomMap degrees l
    where lfull = null newCurNom
          enough = IntMap.size newNomMap >= n
          newNomMap = IntMap.unionWith (+) nomMap nextNoms
          nextNoms = getNomiMap l curNom rel' degrees
          newCurNom = IntMap.keys nextNoms L.\\ nom --all that haven't already nominated someone
          newNom = newCurNom ++ nom --add these new nominators to the running list of nominators


{-
have a list of all the varying parameters


Number of agents -> 120
parameters of holme kim -> as defined above
Threshold -> 0.5
InflMode -> Basic
SelecMode -> Variant

Input:
Number of models to generate
list of k's to test

will generate the models, then generate the leaders using the three strategies
will save for each k the percentage of successes in each of the three strategies
(KRich, Random, Nomination)


ACHTUNG ._.
-}
experiment :: Int -> [Int] -> Gen [(Int, Strategy, Results)]
experiment n ks = do
    models <- replicateM n getSNMCase
    allResults <- forM models $ \rel' ->
        forM ks $ \k ->
            forM [Random, KRich, Nomination] $ \strategy -> do
                resultOne <- runOneGen strategy k rel'
                pure (k, strategy, resultOne)
    return $ aggregate ks (concat $ concat allResults)

{-
Input:
List of values for k
List of experiment results inlcuding k and Strategy.

Output:
Aggregates the results by k and Strategy, to display average values across the generated models.
-}
aggregate :: [Int]  -> [(Int, Strategy, Results)] -> [(Int, Strategy, Results)]
aggregate ks listOfResults =
    [ (k, s, averageResult [x | (k', s', x) <- listOfResults, k == k', s == s'])
    | k <- ks
    , s <- [Random, KRich, Nomination]
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
    divideInt (Results p l s r) i = Results (fI p i) (fI l i) (fIM s i) (M.map (`fI` i) r) where
        fI x y = x / fromIntegral y
        fIM Nothing _ = Nothing
        fIM (Just x) y = Just (x / fromIntegral y)

{-
Input: List of Results
Output: implements sum for [Results]
-}
sumResults :: [Results] -> Results
sumResults = L.foldl' addResults zeroResults where
    zeroResults = Results 0 0 (Just 0) M.empty --TODO check if it works with [] as last argument, sonst rausholen
    addResults (Results a1 b1 c1 d1) (Results a2 b2 c2 d2) = Results (a1+a2) (b1+b2) ((+) <$> c1 <*> c2) (M.unionWith (+) d1 d2)
{-
Data type to store results of single run of experiment.
TODO can be extended if necessary
-}
data Results = Results
    { avgPublic   :: Double                --Initial average degree of non-leader nodes
    , avgLeaders  :: Double                --Initial average degree of leader nodes
    , stab        :: Maybe Double          --Number of iteration until stabilization. Nothing if none was reached.
    , adoptRatios :: M.Map Position Double --Ratio of nodes who hold each position.
    }

{-
Input:
Leader Identification Strategy
0 < k <= totalNrAgs: number of leaders
SNMCase

Output:
Identifies k leaders according to strategy, runs the experiment and return the results.

-}
runOneGen :: Strategy -> Int -> SNMCase -> Gen Results
runOneGen strat k m@(SNMCase snm) = do
    leaders <- snd <$> getLeaders strat k (rel snm M.! flight)
    return $ runOne leaders m



{-
Input:
List of leaders (0 < length <= nr of Agents)
SNMCase

Output:
Intervenes on positions of leaders, runs interleaving and returns results.
-}
runOne :: [Int] -> SNMCase -> Results
runOne leaders (SNMCase snm) = Results avgPublic' avgLeaders' stab' finalDistribution where
    interveneSNM              = snm {dual = M.singleton flight (intervention leaders dual_flight)}
    (avgPublic', avgLeaders') = averageDegrees flightRel leaders
    (finalModel , stab'')     = interleave Variant Basic interveneSNM
    finalDistribution         = posDistribution_t finalModel flight
    flightRel                 = rel snm M.! flight
    stab'                     = fromIntegral <$> stab''
    dual_flight               = dual snm M.! flight



{-
Input:
List of leaders
Dual_t: Dual of a specific topic

Output: New dual_t where the leaders have their new positions after intervention.
-}
intervention :: [Int] -> IntMap (Set Position) -> IntMap (Set Position)
intervention leaders dual_t = IntMap.unionWith S.union dual_t $ IntMap.fromList $ zip leaders (repeat baf)

{-
Input:
Number of models to generate
List of values for k to test

Output:
Runs experiment and prints results.
-}
runAndShow :: Int -> [Int] -> IO()
runAndShow n ks = do
    putStr $ "WELCOME to the experiment zone :) In your experiment, " ++ show n ++ " networks with " ++ show totalNrAgs ++
        " nodes were randomly generated. \n The tested values for the number of leaders were: " ++ show ks ++
        ". Are you READY for the results? \n"
    results <- generate (experiment n ks)
    printTable results



{-
Input: A list of aggregated result.
Output: Prints the results to the console.
-}

printTable :: [(Int, Strategy, Results)] -> IO()
printTable results = do
    let strategyMap = M.fromListWith (++) [ (s, [(k, r)]) | (k, s, r) <- results]
    printStrategy Random (strategyMap M.! Random)
    printStrategy KRich (strategyMap M.! KRich)
    printStrategy Nomination (strategyMap M.! Nomination)


--ACHTUNG . - .
--TODO xs is ordered the wrong way (decreasing)
printStrategy :: Strategy -> [(Int, Results)] -> IO ()
printStrategy s xs = do
    putStrLn $ "\n=== " ++ show s ++ " ==="
    printf "%5s %10s %10s %10s %10s\n"
        "k" "Degree Public" "Degree Leaders" "Rounds" "Ratio"
    mapM_ printRow xs
  where
    printRow (k, Results a' b' c' d') =
        printf "%5d %10.3f %10.3f %10s %10s\n"
            k a' b' (show c') (show d')

--usage in ghci:
{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel

generate (sublistRec 3 [1,2,3,4,5])
-}
--averageDegreesCSNModel <$> (generate arbitrary :: IO CaseSNM)