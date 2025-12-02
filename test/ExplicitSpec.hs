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


--TODO change this, don't need special double -> can write property in testhelpers
    describe "Testing propoerties of update operations" $ do
        prop "Arbitrary SNModel isn't affected by first of two consecutive selec operations" $ do
            \snm i1 i2 -> consecutiveSelec (snm::SNModel) (i1::SpecialDouble) (i2::SpecialDouble)
        prop "Arbitrary SNModel doesn't change with Infl after a Selec 1" $ do
            \snm i1 -> consInflSelecOne  (snm::SNModel) (i1::SpecialDouble)
        prop "Arbitrary SNModel has reflexive relations after a selec operation" $ do
            \snm i1 -> selecMakesRefl (snm::SNModel) (i1::SpecialDouble)
        prop "Arbitrary SNModel has symmetric relations after selec operation" $ do
            \snm i1 -> selecMakesSym (snm::SNModel) (i1::SpecialDouble)


--takes a while atm (updates are slow), maybe comment out when checking other stuff ;)
    describe "Testing the simplify function" $ do
        prop "Arbitrary formula evaluates to the same as it's simplified version on Arbitrary SNModel" $ do
            \snm f -> simplifyWorks (snm::SNModel) (f::Form)


    describe "Tests for formula generation and the simplify function" $ do
        prop "Checks that a generated formula never contains empty lists after Conj or Disj" $ do
            \f -> not $ containsEmpty (f::Form)
        prop "Dummy to see what percentage of generated Forms evaluates to Top or Bot" $ do
            prop_trivialForm
        prop "Dummy to see how many steps until stable" $ do
            prop_numberOfTurns
        prop "Testing if every formula either simplifies to Top/Bot or simplifies to be free of any occurance of top/bot" $ do
            \f -> topBotpurity (f::Form)



{-
TODO think of things to check
(maybe some axioms?)
-}