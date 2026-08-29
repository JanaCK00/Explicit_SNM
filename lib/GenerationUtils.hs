module GenerationUtils where
import Test.QuickCheck (Gen, chooseInt, elements, sublistOf)
import Data.Set (Set)
import qualified Data.Set as S
import Types
import qualified Data.Map as M
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.Vector as V


{-
This module provides helper functions for the random generation of SNModels and Forms.
They use Lists instead of Sets for convenience, and because
the sublist function would require list conversion anyway.
-}


{-
Input:
lmin - lmax: range of length of returned list

Output:
Randomly chooses a length in the given range and returns a random sublist of the chosen length.
-}

sublistOfLength :: Ord a => Int -> Int -> [a] -> Gen [a]
sublistOfLength lmin lmax xs = do
    thisL <- chooseInt (lmin,lmax)
    sublistRec thisL xs

{-
Input:
l: desired length of output >=0
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
Input:
l: number of partitions > 0
xs: list
(Assumptions: length xs >= l)

Output:
Generates a partition of xs with exactly l non-empty subsets.
-}
randomPart :: Int -> [a] -> Gen [[a]]
randomPart 1 xs = return [xs]
randomPart l xs = do
  let n = length xs
  thisLength <- chooseInt (1, n - l + 1) --make sure the rest of the (l-1) partitions still get at least one element each
  let (first, rest) = splitAt thisLength xs
  restPart <- randomPart (l-1) rest
  return $ first : restPart




{-
Input:
nrAgs: Stands for agents [0..nrAgs-1].

Output:
Generates a random Relation between agents [0..nrAgs-1].
-}
randomRel :: Int -> Gen Relation
randomRel nrAgs = do
  list <- randomRelList nrAgs nrAgs
  return $ V.fromList list

--second argument is the recursively decreasing one
randomRelList :: Int -> Int -> Gen [AgentSet]
randomRelList _ 0 = return []
randomRelList nrAgs n = do
    thisAgsFriends <- IntSet.fromList <$> sublistOf [0..nrAgs-1]
    rest <- randomRelList nrAgs (n-1)
    return $ thisAgsFriends:rest


{-
Input:
nrAgs: Stands for agents [0..nrAgs-1].
tpcs: List of Topics (duplicate-free)

Output:
Generates an random relation for each topic and returns the corresponding map.
-}
randomRelMap :: Int -> [Topic] -> Gen (M.Map Topic Relation)
randomRelMap _ [] = return M.empty
randomRelMap nrAgs (t:tpcs) =  do
    thisTpcsRel <- randomRel nrAgs
    rest <- randomRelMap nrAgs tpcs
    return $ M.insert t thisTpcsRel rest


{-
Input:
pos: Set of Positions (assumed to belong to one topic)
ags: List of Agents (duplicate free)

Output:
Generates a random dualVal for one topic (Map from Agent to subset of those Positions) and returns the corresponding map.
-}
randomDualValT :: Set Position -> [Agent] -> Gen (IntMap (Set Position))
randomDualValT _ [] = return IntMap.empty
randomDualValT pos (ag:ags) = do
    thisAgsPos <- subsetOf pos
    rest <- randomDualValT pos ags
    if S.size thisAgsPos > 0 then --only include Agents in the map that take at least one position
      return $ IntMap.insert ag thisAgsPos rest
    else
      return rest


{-
Input:
posMap: positions map (Topic to Set of Positions)
ags: List of Agents

Output:
Applies randomDualValT for each topic and returns a randomly generated dualVal.
-}
randomDualValMap :: M.Map Topic (Set Position) -> [Agent] -> Gen (M.Map Topic (IntMap (Set Position)))
randomDualValMap posMap ags = traverse (`randomDualValT` ags) posMap



{-
Input:
ts: List of Topics
ps: List of Positions
(Assumptions: both duplicate free & non-empty, length ps>=length ts)

Output:
Generates a mapping from topics to sets of positions (pairwise disjoint, non-empty).
-}
randomPosMap :: [Topic] -> [Position] -> Gen (M.Map Topic (Set Position))
randomPosMap ts ps = do
  partition <- randomPart (length ts) ps
  return $ M.fromList $ zipWith (\t partP -> (t, S.fromList partP)) ts partition




{-
Checks if a given list has length between lower and upper.
Used in random generation for Form
-}
isOfSizeBetween :: Int -> Int -> [a] -> Bool
isOfSizeBetween lower upper xs = lower <= l &&  l <= upper where
  l = length xs


--Returns a random subset. Equivalent to sublistOf on lists.
subsetOf :: (Ord a) => Set a -> Gen (Set a)
subsetOf = fmap S.fromList . sublistOf . S.toList