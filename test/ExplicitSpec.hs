module ExplicitSpec where

--TODO only do necessary imports
import Test.Hspec (describe, it, shouldBe, Spec)
import Test.Hspec.QuickCheck (prop)

import SNModel
import Semantics
import TestHelpers

spec :: Spec
spec = do
    describe "Testing a simple tautology" $ do
        prop "Arbitrary SNModel fulfills the simple tautology" $ do
            \snm -> (snm::SNModel) |= taut
    describe "Testing for full Maps" $ do
        prop "Arbitrary SNModel has complete Relations maps" $ do
            \snm -> fullRel (snm::SNModel)
        prop "Arbitrary SNModel has a complete Valuation map" $ do
            \snm -> fullVal (snm::SNModel)
    --describe "Testing a falsifiable formula" $ do
        --prop "Arbitrary SNModel fulfills falsifiable formula" $ do
            -- \snm -> (snm::SNModel) |= propo1
    {-
    will only be useful if I change generation away from using default sets
    -}
    describe "Testing for non-empty sets" $ do
        prop "Arbitrary SNModel has non-empty set of agents"  $ do
            \snm -> nonEmptyAgs (snm::SNModel)
        prop "Arbitrary SNModel has non-empty set of agents"  $ do
            \snm -> nonEmptyTpcs (snm::SNModel)
        prop "Arbitrary SNModel has non-empty set of agents"  $ do
            \snm -> nonEmptyPos (snm::SNModel)

    describe "Testing for valid positions (topics map to only positions that belong to them)" $ do
        prop "Arbitrary SNModel has valid positions map" $ do
            \snm -> validPositions (snm::SNModel)

    {-describe "Testing for no duplicates in the model" $ do
        prop "Arbitrary SNModel has no duplicates in fields" $ do
            \snm -> noDuplicates (snm::SNModel)
        -}

    describe "Testing if all properties are fulfilled" $ do
        prop "Arbitrary SNModel is a social networks model" $ do
            \snm -> isValidSNModel (snm::SNModel)

--TODO find out how to get random valud taus here....

    describe "Testing if consecutive application of friendship selection doesn't depend on first" $ do
        prop "Arbitrary SNModel isn't affected by first of two consecutive selec operations" $ do
            \snm -> consecutiveSelec (snm::SNModel)

    describe "Testing if infl after Selec 1 doesn't do anything" $ do
        prop "Arbitrary SNModel doesn't change with Infl after a Selec 1" $ do
            \snm ->consInflSelecOne  (snm::SNModel)




{-
TODO think of things to check
(maybe some axioms?)
-}