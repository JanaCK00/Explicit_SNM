module ExplicitSpec where

--TODO only do necessary imports
import Test.Hspec (describe, Spec)
import Test.Hspec.QuickCheck (prop)

import SNModel
import Semantics
import TestHelpers
import Syntax
import SNModel (isValidSNModel, valToDualVal)

spec :: Spec
spec = do
    describe "Testing a simple tautology" $ do
        prop "Arbitrary SNModel fulfills the simple tautology" $ do
            \snm -> (snm::SNModel) |= taut


    {-
    will only be useful if I change generation away from using default sets
    -}
{- were all falsified, as expected :)
        prop "All SNModels map every agent in all dualVal_t (should be falsified)" $ do
            \snm -> fullDualVal (snm::SNModel)
        prop "All SNModels map every agent in all dualVal_t after Basic Infl(should be falsified)" $ do
            \snm i1 -> fullDualValBasicInfl (i1::Double) (snm::SNModel)
        prop "All SNModels map every agent in all dualVal_t after Basic Selec(should be falsified)" $ do
            \snm i1 -> fullDualValBasicSelec (i1::Double) (snm::SNModel)
        prop "All SNModels map every agent in all dualVal_t after Variant Infl (should be falsified)" $ do
            \snm i1 -> fullDualValVariantInfl (i1::Double) (snm::SNModel)
        prop "All SNModels map every agent in all dualVal_t after Variant Selec(should be falsified)" $ do
            \snm i1 -> fullDualValVariantSelec (i1::Double) (snm::SNModel)

-}



    describe "Testing if all properties are fulfilled" $ do
        prop "Arbitrary SNModel is a social networks model" $ do
            \snm -> fst $ isValidSNModel (snm::SNModel)
        prop "Translation between valuation and dual valuation works." $ do
            \snm -> valToDualVal (val snm) == dualVal snm

    describe "Testing propoerties of basic update operations" $ do
        prop "Infl Basic leaves relations of arbitrary SNModel unchanged" $ do
            \snm i1 -> inflNotChangeRel (i1::Double) (snm::SNModel)
        prop "Selec Basic leaves positions of agents of arbitrary SNModel unchanged" $ do
            \snm i1 -> selecNotChangeDualVal (i1::Double) (snm::SNModel)
        prop "Arbitrary SNModel isn't affected by first of two consecutive selec operations" $ do
            \snm i1 i2 -> consecutiveSelec (snm::SNModel) (i1::Double) (i2::Double)
        prop "Arbitrary SNModel doesn't change with Infl Basic after a Selec Basic 1 (except for Infl 0)" $ do
            \snm i1 -> consInflSelecOne  (snm::SNModel) (i1::Double)
        prop "Arbitrary SNModel has reflexive relations after a selec operation" $ do
            \snm i1 -> selecMakesRefl (snm::SNModel) (i1::Double)
        prop "Arbitrary SNModel has symmetric relations after selec operation" $ do
            \snm i1 -> selecMakesSym (snm::SNModel) (i1::Double)
        prop "Dummy to see how many steps until stable in an interleavin of Basic Selec and Basic Infl" $ do
            prop_numberOfTurns
        prop "Updates on Example 2 from paper Smets et al (2020) are correctly computed (SelecBasic, InflBasic)" $ do
            exPaperstep1 == updSelecBasic 0.5 exPaperstep0 &&
                exPaperstep2 == updInflBasic 0.5 exPaperstep1 &&
                exPaperstep3 == updSelecBasic 0.5 exPaperstep2 &&
                exPaperstep4 == updInflBasic 0.5 exPaperstep3 &&
                exPaperstep5 == updSelecBasic 0.5 exPaperstep4 &&
                exPaperstep5 == updInflBasic 0.5 exPaperstep5


    describe "Testing properties of combined variant update operations" $ do
        prop "Arbitrary SNModel isn't affected by Selec Variant tau1 if a Selec Varient tau2 is applied after (with tau2>=tau1)" $ do
            \snm i1 i2 -> variantSelecGrowingTau (i1::Double) (i2::Double)  (snm::SNModel)
        prop "Infl Variant leaves relations of arbitrary SNModel unchanged" $ do
            \snm i1 -> inflVarNotChangeRel (i1::Double) (snm::SNModel)
        prop "Selec Variant leaves positions of agents of arbitrary SNModel unchanged" $ do
            \snm i1 -> selecVarNotChangeDualVal (i1::Double) (snm::SNModel)
        prop "Arbitrary SNModel has reflexive relations after a variant selec operation" $ do
            \snm i1 -> selecMakesReflVariant (snm::SNModel) (i1::Double)
        prop "A Selec Variant operation on an arbitrary SNModel doesn't increases the number of reachable agents for any agent" $ do
            \snm i1 -> noGrowingReachable (i1::Double) (snm::SNModel)
        prop "Dummy to see how many steps until stable variant" $ do
            prop_numberOfTurnsVariant
        prop "Updates on Example 4 from paper Smets et al (2020) are correctly computed (SelecBasic, InflVariant)" $ do
            exPaperVarstep1 == updSelecBasic 0.5 exPaperVarstep0 &&
                exPaperVarstep2 == updInflVariant 0.5 exPaperVarstep1 &&
                exPaperVarstep3 == updSelecBasic 0.5 exPaperVarstep2 &&
                exPaperVarstep4 == updInflVariant 0.5 exPaperVarstep3 &&
                exPaperVarstep5 == updSelecBasic 0.5 exPaperVarstep4 &&
                exPaperVarstep5 == updInflVariant 0.5 exPaperVarstep5
        prop "Updates on own example are correctly computed (InflVariant, SelecVariant)" $ do
            exOwnstep1 == updInflVariant 0.5 exOwnstep0 &&
                exOwnstep2 == updSelecVariant 0.5 exOwnstep1 &&
                exOwnstep3 == updInflVariant 0.5 exOwnstep2 &&
                exOwnstep4 == updSelecVariant 0.5 exOwnstep3 &&
                exOwnstep4 == updInflVariant 0.5 exOwnstep4

        {- both have been falsified :)
        prop "Keyword Testing part of SelecVariant:  makeReflexive never makes a difference in transclosure (should be falsified)" $ do
            \snm -> testmakeReflexive (snm::SNModel)
        prop "Keyword Testing part of SelecVariant: combined Topics rel is always reflexive (should be falsified)" $ do
            \snm -> testcombinedTopicsRel (snm::SNModel)
-}



{-
SECTION: Syntax
-}
    describe "Testing the simplify function" $ do
        prop "Arbitrary Form evaluates to the same as its simplified version on Arbitrary SNModel" $ do
            \snm f -> simplifyWorks (snm::SNModel) (f::Form)


    describe "Tests for Form generation" $ do
        prop "Checks that a generated formula never contains empty lists after Conj or Disj" $ do
            \f -> not $ containsEmpty (f::Form)
        prop "Checks that a generated formula never contains too long lists after Conj or Disj" $ do
            \f -> not $ containsLongList (f::Form)
        prop "Dummy to see what percentage of generated Forms simpifies to Top or Bot" $ do
            \f -> prop_trivialForm (f::Form)
        prop "Testing if every formula either simplifies to Top/Bot or simplifies to be free of any occurance of top/bot" $ do
            \f -> topBotpurity (f::Form)
        prop "Testing if every Form is mode consistent" $ do
            \f -> isModeCons (f::Form)

