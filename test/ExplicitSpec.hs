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
TODO think of things to check
(is there much more for the models without updates? bc the relations don't have to fulfill anything...
(maybe some axioms?)
-}