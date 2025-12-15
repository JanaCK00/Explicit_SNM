module ExplicitSpec where

--TODO only do necessary imports
import Test.Hspec (describe, it, shouldBe, Spec)
import Test.Hspec.QuickCheck (prop)

import SNModel
import Semantics
import TestHelpers
import Syntax

spec :: Spec
spec = do
    describe "Testing a simple tautology" $ do
        prop "Arbitrary SNModel fulfills the simple tautology" $ do
            \snm -> (snm::SNModel) |= taut
    describe "Testing for full Maps" $ do
        prop "Arbitrary SNModel has complete Relations maps" $ do
            \snm -> fullRel (snm::SNModel)
        prop "Arbitrary SNModel has full dual Maps" $ do
            \snm -> fullDual (snm::SNModel)
        --prop "Arbitrary SNModel has a complete Valuation map" $ do
            -- \snm -> fullVal (snm::SNModel)
    --describe "Testing a falsifiable formula" $ do
        --prop "Arbitrary SNModel fulfills falsifiable formula" $ do
            -- \snm -> (snm::SNModel) |= propo1
    {-
    will only be useful if I change generation away from using default sets
    -}
    describe "Testing for non-empty sets" $ do
        --prop "Arbitrary SNModel has non-empty set of agents"  $ do
           -- \snm -> nonEmptyAgs (snm::SNModel)
        prop "Arbitrary SNModel has non-empty set of topics"  $ do
            \snm -> nonEmptyTpcs (snm::SNModel)
        prop "Arbitrary SNModel has non-empty set of positions"  $ do
            \snm -> nonEmptyPos (snm::SNModel)

{-}
    describe "Testing for valid positions (topics map to only positions that belong to them)" $ do
        prop "Arbitrary SNModel has valid positions map" $ do
            \snm -> validPositions (snm::SNModel)

            -}
    describe "Testing for unqique positions across topics" $ do
        prop "Arbitrary SNModel has pairwise disjoint Positions across Topics" $ do
            \snm -> disjointPositionSets (snm::SNModel)

    {-describe "Testing for no duplicates in the model" $ do
        prop "Arbitrary SNModel has no duplicates in fields" $ do
            \snm -> noDuplicates (snm::SNModel)
        -}

    describe "Testing if all properties are fulfilled" $ do
        prop "Arbitrary SNModel is a social networks model" $ do
            \snm -> isValidSNModel (snm::SNModel)


    describe "Testing propoerties of update operations" $ do
        prop "Arbitrary SNModel isn't affected by first of two consecutive selec operations" $ do
            \snm i1 i2 -> consecutiveSelec (snm::SNModel) (i1::Double) (i2::Double)
        prop "Arbitrary SNModel doesn't change with Infl after a Selec 1 (except for Infl 0)" $ do
            \snm i1 -> consInflSelecOne  (snm::SNModel) (i1::Double)
        prop "Arbitrary SNModel has reflexive relations after a selec operation" $ do
            \snm i1 -> selecMakesRefl (snm::SNModel) (i1::Double)
        prop "Arbitrary SNModel has symmetric relations after selec operation" $ do
            \snm i1 -> selecMakesSym (snm::SNModel) (i1::Double)
        prop "Dummy to see how many steps until stable" $ do
            prop_numberOfTurns


    describe "Testing the simplify function" $ do
        prop "Arbitrary BasicForm evaluates to the same as its simplified version on Arbitrary SNModel" $ do
            \snm f -> simplifyWorksBasic (snm::SNModel) (f::BasicForm)
        prop "Arbitrary VariantForm evaluates to the same as its simplified version on Arbirtary SNModel" $ do
            \snm f -> simplifyWorksVariant (snm::SNModel) (f::VariantForm)


    describe "Tests for BasicForm generation" $ do
        prop "Checks that a generated formula never contains empty lists after Conj or Disj" $ do
            \f -> not $ containsEmptyBasic (f::BasicForm)
        prop "Dummy to see what percentage of generated Forms simpifies to Top or Bot" $ do
            prop_trivialFormBasic
        prop "Testing if every formula either simplifies to Top/Bot or simplifies to be free of any occurance of top/bot" $ do
            \f -> topBotpurityBasic (f::BasicForm)
        prop "Testing if every BasicForm is mode consistent" $ do
            \f -> modeConsistentBas (f::BasicForm)

    describe "Tests for VariantForm generation" $ do
        prop "Checks that a generated formula never contains empty lists after Conj or Disj" $ do
            \f -> not $ containsEmptyVariant (f::VariantForm)
        prop "Dummy to see what percentage of generated Forms simpifies to Top or Bot" $ do
            prop_trivialFormVariant
        prop "Testing if every formula either simplifies to Top/Bot or simplifies to be free of any occurance of top/bot" $ do
            \f -> topBotpurityVariant (f::VariantForm)
        prop "Testing if every VariantForm is mode consistent" $ do
            \f -> modeConsistentVar (f::VariantForm)



{-
TODO think of things to check
-}