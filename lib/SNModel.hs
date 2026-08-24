{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module SNModel where

import Test.QuickCheck
  ( Arbitrary (..)
  , Gen)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S

import Data.Set (Set)
import qualified Data.IntSet as IntSet
import GenerationUtils
import Types
import qualified Data.Vector as V
import Text.Read (readMaybe)


{-
This module defines Social Networks Models.
It also provides random generation of Social Networks Models.
-}

--------------------------------------------------------------------------------
-- Definition of Social Networks Models
--------------------------------------------------------------------------------

{-
Social Networks Models are relational Kripke models, by definition with:

 - a non-empty, (finite) set of agents as the domain
 - a non-empty, (finite) set of topics
 - for each topic a non-empty, finite set of positions on the topic (These sets are pairwise disjoint.)
 - a binary relation for each topic (= social network).)
   (These don't have to satisfy any specific properties (such as symmetry or reflexivity).)
-}


{-
Social Networks Models are represented using the data type SNModel, consisting of the following fields:

- nrAgents:  An Int representing the number of Agents. It defines the set of agents ([0...nrAgents-1]).
- positions: A map from Topics to sets of Positions. It defines the set of topics and the corresponding sets of positions.
- rel:       A map from Topics to Relations. It defines the binary relation for each topic.
- dualVal:   A map from Topics to dual valuations (maps from Agents to sets of Positions).
             It defines the set of positions each agent has adopted for each topic.
            Agents that haven't adopted any position of a topic are omitted from the map.

SNModels are assumed to follow the definition of Social Networks Models specified above.
Additionally, the Topic (T 0) is reserved for internal use (see Semantics.hs).
These restrictions aren't enforced in construction, but can be checked using the function (fst $ isWellFormedSNModel)
-}
data SNModel = SNM
 { nrAgents :: Int
 , positions :: M.Map Topic (Set Position)
 , rel :: M.Map Topic Relation
 , dualVal :: M.Map Topic (IntMap (Set Position))
 } deriving (Eq)


--------------------------------------------------------------------------------
-- Predicates for SNModel
--------------------------------------------------------------------------------

{-
Checks if an SNModel is a well-formed Social Networks Model.
If yes: Returns a tuple of (True, []) if it is well-formed.
Otherwise: Returns a tuple of (False, xs), where xs is a list of error messages.
-}
isWellFormedSNModel :: SNModel -> (Bool, [String])
isWellFormedSNModel snm = (isWellFormed, errorList) where
    errorList = map snd $ filter (not . fst) $ isWellFormedSNModelList snm
    isWellFormed = null errorList


isWellFormedSNModelList :: SNModel -> [(Bool, String)]
isWellFormedSNModelList (SNM ags' pos' rel' dualVal') =
  [ isWellFormednrAgents ags'
  , isWellFormedPositions pos'
  , isWellFormedRel ags' pos' rel'
  , isWellFormedDualVal ags' pos' dualVal']




{-
Checks if the provided number is a well-formed nrAgents for an SNModel.
Returns a tuple of (predicate, error message).
-}
isWellFormednrAgents :: Int -> (Bool, String)
isWellFormednrAgents n | n > 0 = (True, "")
                       | otherwise = (False, "Invalid number of agents. You need at least one agent.")


{-
Checks if a provided map from Topics to Positions is a well-formed positions for an SNModel.
Returns a tuple of (predicate, error message).
-}
isWellFormedPositions :: M.Map Topic (Set Position) -> (Bool, String)
isWellFormedPositions pos' = (wellFormedPos, unlines errorList) where
    errorList = map snd $ filter (not . fst) [wellFormedTs, wellFormedTps, disjoint]
    wellFormedPos = null errorList
    wellFormedTs = (M.size pos' > 0 && (T 0) `M.notMember` pos', "You need at least one topic (T 0 reserved).")
    wellFormedTps = (not (any null pos') , "You need at least one position per topic.")
    disjoint = (S.size (S.unions pos') == foldr ((+) . S.size) 0 pos', "Positions can't belong to more than one topic.")


{-
Checks if a provided map from Topics to Relations is a well-formed rel for an SNModel.
Returns a tuple of (predicate, error message).
-}
isWellFormedRel :: Int -> M.Map Topic (Set Position) -> M.Map Topic Relation -> (Bool, String)
isWellFormedRel ags' pos' rel' = (wellFormedRel, unlines errorList) where
    errorList = map snd $ filter (not . fst) [wellFormedTops, wellFormedVecs, wellFormedAgs]
    wellFormedRel = null errorList
    wellFormedTops = (M.keys pos' == M.keys rel', "You have to enter a relation for each topic you defined (and no others).")
    wellFormedVecs = (all (\v -> V.length v == ags') rel', "Not all of your relations have the right size.")
    wellFormedAgs = (all (all (allElems (<= ags'))) rel', "Your relations contain agents that you haven't defined.")
    allElems predicate ks = all predicate (IntSet.toList ks)


{-
Checks if a provided map from Topics to maps from Agennts to sets of Positions is a well-formed dualVal for an SNModel.
Returns a tuple of (predicate, error message).
-}
isWellFormedDualVal :: Int -> M.Map Topic (Set Position) -> M.Map Topic (IntMap (Set Position)) ->  (Bool, String)
isWellFormedDualVal ags' pos' dualVal' = (wellFormedDualVal, unlines errorList) where
    errorList = map snd $ filter (not . fst) [wellFormedTops, wellFormedPos, wellFormedAgs]
    wellFormedDualVal = null errorList
    wellFormedTops = (M.keys pos' == M.keys dualVal', "You have to enter a dual valuation for each topic you defined (and no others).")
    wellFormedPos = (allWithKey (\t iPs -> all (`S.isSubsetOf` (pos' M.! t)) iPs) dualVal', "Your dual valuation assigns positions that you haven't defined.")
    wellFormedAgs = (all (\m -> null m || maximum (IntMap.keys m) < ags') dualVal', "Your dual valuation contains agents that you haven't defined.")
    allWithKey predicate = M.foldrWithKey (\k v acc -> predicate k v && acc) True


--------------------------------------------------------------------------------
-- Helpers for construction of SNModels
--------------------------------------------------------------------------------


{-
Takes an SNModel and returns the valuation.

Each Topic is mapped to a map from Positions to the set of Agents that have adopted that Position.
Positions that are adopted by no Agent are not in the map.
-}
val :: SNModel -> M.Map Topic (M.Map Position AgentSet)
val snm = dualValtoVal $ dualVal snm

{-
Taes an SNModel and a Topic and returns the valuation for that Topic.
-}
{-# ANN val_t "HLint: ignore Use camelCase" #-}
val_t :: SNModel -> Topic -> M.Map Position AgentSet
val_t snm t = dualValToVal_t $ dualVal' M.! t  where
  dualVal' = dualVal snm


{-
Translation from dual valuation to valuation.
-}
dualValtoVal :: M.Map Topic (IntMap (Set Position)) -> M.Map Topic (M.Map Position AgentSet)
dualValtoVal = M.map dualValToVal_t

{-
Translation from dual valuation for one topic to valuation for the topic.
-}
{-# ANN dualValToVal_t "HLint: ignore Use camelCase" #-}
dualValToVal_t :: IntMap (Set Position) -> M.Map Position AgentSet
dualValToVal_t dualVal_t =  M.fromListWith IntSet.union
    [ (p, IntSet.singleton i)
    | (i, ps) <- dualVal_t_list
    , p <- S.toList ps
    ] where
  dualVal_t_list =  IntMap.toList dualVal_t


{-
Translation from valuation to dual valuation.
Agents that don't hold any position of that topic don't appear in the map.
-}
valToDualVal :: M.Map Topic (M.Map Position AgentSet) -> M.Map Topic (IntMap (Set Position))
valToDualVal = M.map valToDualVal_t

{-
Translation from valuation for one topic to dual valuation for the topic.
-}
{-# ANN valToDualVal_t "HLint: ignore Use camelCase" #-}
valToDualVal_t :: M.Map Position AgentSet -> IntMap (Set Position)
valToDualVal_t val_t' = IntMap.fromListWith S.union
    [ (i, S.singleton p)
    | (p, is) <- val_t_list
    , i <- IntSet.toList is
    ] where
  val_t_list = M.toList val_t'



{-
Interactive construction of well-formed SNModels.
Will ask for user input for each component, feedback directly if the component is well-formed.
Returns an SNModel after each component has been entered.

Usage in ghci:
myModel <- makeMyModel

TODO can't handle backspace in input.
-}
makeMyModel :: IO SNModel
makeMyModel = do

  --Ask for Agents.
  ags' <- askUntilValid "Enter the number of agents:" isWellFormednrAgents

  putStrLn $ "Your defined agents are [0.." ++ show (ags' - 1) ++ "] \n"

  --Ask for Topics and Positions.
  posInput <- askUntilValid
        (unlines ["Enter topics and their positions."
        , "Format: [(Topic, [Position])]"
        , "Example: [(T 1, [P 1, P 2])]"])
        (isWellFormedPositions . toPositions)

  let pos' = toPositions posInput
  putStrLn $ "Your defined topics and positions are " ++ showPositions pos' ++ "\n"

  --Ask for Relations.
  --TODO maybe allow emptyRel, fullRel?
  relInput <- askUntilValid
        (unlines
        ["Enter the relation for each topic."
        , "For each topic, give a list of friends for each agent. Agents with no friends get an empty list."
        , "Format: [(Topic, [[Agent]])]"
        , "Example: [(T 1, [[0,1], [0,1,2], []])]"])
        (isWellFormedRel ags' pos' . toRelations)


  let rel' = toRelations relInput

  --Ask for either dual valuation or valuation.
  dualValOrVal <- askUntilValid
    (unlines
        [ "You can choose to enter either the dual valuation or the valuation."
        , "Which one would you like to enter? Please enter your choice."
        , "Format: DualVal or Val"
        ])
    (const (True, ""))

 --Ask for dual valuation.
  dualVal' <- case dualValOrVal of
    DualVal -> do
        dualInput <- askUntilValid
            (unlines
                [ "Enter the positions adopted by the agents for each topic."
                , "Agents with no adopted positions can be omitted."
                , "Format: [(Topic, [(Agent, [Position])])]"
                , "Example: [(T 1, [(0,[P 1]), (1,[P 1,P 2])])]"
                ])
            (isWellFormedDualVal ags' pos' . toDualVal)

        return $ toDualVal dualInput

 --Ask for valuation.
    Val -> do
        valInput <- askUntilValid
            (unlines
                [ "Enter the valuation."
                , "Format: [(Topic, [(Position, [Agent])])]"
                , "Example: [(T 1, [(P 1, [0,1]), (P 2, [1])])]"
                ])
            (isWellFormedDualVal ags' pos' . valToDualVal . toVal)

        return $ valToDualVal (toVal valInput)

 --Construct the SNModel.
  let snm = SNM ags' pos' rel' dualVal'
  let (wellFormedSNM, errorList) = isWellFormedSNModel snm --This is just a safety double-check.
  if not wellFormedSNM then error $ unlines errorList --Prints error messages, if SNModel is not well-formed.
    else return snm




{-
Helper function for interactive construction of SNModels. Will ask until the user has entered a well-formed input.
Can handle both invalid format and ill-formed input as defined by the provided wellFormedPred.

Input:
prompt: The prompt displayed to the user.
wellFormedPred: A function that checked whether the input is well-formed (and provides an errormessage if it isn't).
-}
askUntilValid :: Read a => String -> (a -> (Bool, String)) -> IO a
askUntilValid prompt wellFormedPred = do
  putStrLn prompt
  input <- getLine

  case readMaybe input of
    Nothing -> do
      putStrLn "\n Invalid input format. Please try again. \n"
      askUntilValid prompt wellFormedPred

    Just x -> do
      let (isWellFormed, errorMsg) = wellFormedPred x

      if isWellFormed
        then return x
        else do
          putStrLn $ "Ill-formed input." ++ errorMsg ++ "\n"
          askUntilValid prompt wellFormedPred


--Translation from input format to component format.
toPositions :: [(Topic, [Position])] -> M.Map Topic (S.Set Position)
toPositions tps = M.map S.fromList (M.fromList tps)

--Translation from input format to component format.
toRelations :: [(Topic, [[Int]])] -> M.Map Topic Relation
toRelations xs = M.map (V.fromList . map IntSet.fromList) $ M.fromList xs

--Translation from input format to component format.
toDualVal :: [(Topic, [(Int, [Position])])] -> M.Map Topic (IntMap.IntMap (S.Set Position))
toDualVal = M.fromList  . map (\(t, ags) -> (t, IntMap.fromList
            [ (a, S.fromList ps)
            | (a, ps) <- ags
            ]))

--Translation from input format to component format.
toVal :: [(Topic, [(Position , [Agent])])] -> M.Map Topic (M.Map Position IntSet.IntSet)
toVal = M.fromList . map (\(t, ps) -> (t, M.fromList
          [ (p, IntSet.fromList ags)
          | (p, ags) <- ps
          ]))


--Used to give the option of entering either the dual valuation or the valuation.
data RepType = DualVal | Val deriving (Eq, Ord, Show, Read)



--------------------------------------------------------------------------------
-- Random generation of SNModels
--------------------------------------------------------------------------------


{-
Input:
n: number of agents
tps: a list of tuples (Topic, [Position])

Output:
Returns a randomly generated SNmodel if the input is well-formed.

Example input in ghci:
import Test.QuickCheck
generate (getRandomSNModel 5 [(T 1, [P 1, P 2]), (T 2, [P 3, P 4])])

This example will generate a random SNModel with 5 agents and two topics having 2 positions each.
-}
getRandomSNModel :: Int -> [(Topic, [Position])] -> Gen SNModel
getRandomSNModel n tps | not wellFormedAgs = error errorAgs
                       | not wellFormedPos = error errorPos
                       | otherwise = do
                                     dualVal' <- randomDualValMap pos [0..n-1]
                                     rel' <- randomRelMap n (M.keys pos)
                                     return $ SNM n pos rel' dualVal'
        where
        pos = M.map S.fromList $ M.fromList tps --make the input a Map
        (wellFormedPos, errorPos) = isWellFormedPositions $ toPositions tps
        (wellFormedAgs, errorAgs) = isWellFormednrAgents n


{-
Default values for arbitrary generation. (defining the domain for Agents, Topics and Positions that can occur)
These are necessary to make sure arbitrary Forms match arbitrary SNModels.
-}
defaultNrAgs, nrTpcs, nrPosTotal :: Int
defaultNrAgs = 120
nrTpcs = 2
nrPosTotal = 6 --number of positions in total, assumes nrPosTotal >= nrTpcs

{-
  Generates an arbitrary SNModel based on the defined default values.
  The default values ensure that the arbitrary Forms match the arbitrary SNModels.
-}
instance Arbitrary SNModel where
  arbitrary = do
    let tpcs = map T [1..nrTpcs]
        pos = map P [1..nrPosTotal]
    randomTPMap <- randomPosMap tpcs pos
    randomRels <- randomRelMap defaultNrAgs tpcs
    randomDualVal <- randomDualValMap randomTPMap [0..defaultNrAgs-1]
    return (SNM defaultNrAgs randomTPMap randomRels randomDualVal)

{-
usage in ghci:
import Test.QuickCheck
myModel <- generate arbitrary :: IO SNModel
-}



--------------------------------------------------------------------------------
-- Some helpers for SNModels
--------------------------------------------------------------------------------


{-
Takes a SNModel and makes full relations for all topics.
Used in Semantics.hs for Selec Basic 0.
-}
makeFullRelModel :: SNModel -> SNModel
makeFullRelModel m@(SNM nrAgents' pos' _ _) = m { rel = fullRels } where
    fullRels = M.fromList $ map (, fullRel) (M.keys pos')
    fullRel = makeFullRel nrAgents'


{-
Takes a SNModel and makes all its relations reflexive.
Can be used for SNModel construction.
Is currently used in testing.
-}
makeReflModel :: SNModel -> SNModel
makeReflModel m@(SNM _ _ rel' _) = m {rel = M.map makeReflexive rel'}

{-
Takes a SNmodel and makes all its relations symmetric.
Can be used for SNModel construction.
Is currently used in testing.
-}
makeSymModel :: SNModel -> SNModel
makeSymModel m@(SNM _ _ rel' _) = m {rel = M.map makeSymmetric rel'}





--Makes SNModels more readable in the console (especially for smaller models).
instance Show SNModel where
    show snm = unlines
            [ ""
            , "SNModel"
            , ""
            , "Number of Agents: " ++ show (nrAgents snm)
            , ""
            , "Topics and Positions:"
            , showPositions (positions snm)
            , ""
            , "Relations:"
            , showRelations (rel snm)
            , ""
            , "Dual valuation:"
            , showDualVal (dualVal snm)
            ]


showPositions :: M.Map Topic (Set Position) -> String
showPositions = unlines . map (\(t, ps) -> show t ++ ": " ++ show (S.toList ps)) . M.toList

showRelations :: M.Map Topic Relation -> String
showRelations = unlines . map (\(t, r) -> show t ++ ":\n" ++ showRelation r) . M.toList

showRelation :: Relation -> String
showRelation r = unlines [show i ++ ": " ++ show (IntSet.toList neighbours)
                        | (i, neighbours) <- V.toList (V.indexed r)]

showDualVal :: M.Map Topic (IntMap (Set Position)) -> String
showDualVal = unlines . map (\(t, d) -> show t ++ ":\n" ++ showDualVal_t d) . M.toList

{-# ANN showDualVal_t "HLint: ignore Use camelCase" #-}
showDualVal_t :: IntMap (Set Position) -> String
showDualVal_t d = unlines [show ag ++ ": " ++ show (S.toList ps) | (ag, ps) <- IntMap.toList d]



