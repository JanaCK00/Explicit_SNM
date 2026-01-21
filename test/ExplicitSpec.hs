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
        prop "Arbitrary SNModel has no dual mapping any agent to the empty set" $ do
            \snm -> nonEmptyDualmapping (snm::SNModel)
        prop "Arbitrary SNModel has no dual mapping any agent to the empty set after Basic Infl" $ do
            \snm i1 -> nonEmptyDualmappingBasicInfl (i1::Double) (snm::SNModel)
        prop "Arbitrary SNModel has no dual mapping any agent to the empty set after Basic Selec" $ do
            \snm i1 -> nonEmptyDualmappingBasicSelec (i1::Double) (snm::SNModel)
        prop "Arbitrary SNModel has no dual mapping any agent to the empty set after Variant Infl" $ do
            \snm i1 -> nonEmptyDualmappingVariantInfl (i1::Double) (snm::SNModel)
        prop "Arbitrary SNModel has no dual mapping any agent to the empty set after Variant Selec" $ do
            \snm i1 -> nonEmptyDualmappingVariantSelec (i1::Double) (snm::SNModel)

{- were all falsified, as expected :)
        prop "All SNModels map every agent in all dual_t (should be falsified)" $ do
            \snm -> fullDual (snm::SNModel)
        prop "All SNModels map every agent in all dual_t after Basic Infl(should be falsified)" $ do
            \snm i1 -> fullDualBasicInfl (i1::Double) (snm::SNModel)
        prop "All SNModels map every agent in all dual_t after Basic Selec(should be falsified)" $ do
            \snm i1 -> fullDualBasicSelec (i1::Double) (snm::SNModel)
        prop "All SNModels map every agent in all dual_t after Variant Infl (should be falsified)" $ do
            \snm i1 -> fullDualVariantInfl (i1::Double) (snm::SNModel)
        prop "All SNModels map every agent in all dual_t after Variant Selec(should be falsified)" $ do
            \snm i1 -> fullDualVariantSelec (i1::Double) (snm::SNModel)

-}


    describe "Testing for unqique positions across topics" $ do
        prop "Arbitrary SNModel has pairwise disjoint Positions across Topics" $ do
            \snm -> disjointPositionSets (snm::SNModel)



    describe "Testing if all properties are fulfilled" $ do
        prop "Arbitrary SNModel is a social networks model" $ do
            \snm -> isValidSNModel (snm::SNModel)


    describe "Testing propoerties of basic update operations" $ do
        prop "Basic Infl operation leaves relations of arbitrary SNModel unchanged" $ do
            \snm i1 -> inflNotChangeRel (i1::Double) (snm::SNModel)
        prop "Basic Selec operation leaves positions of agents of arbitrary SNModel unchanged" $ do
            \snm i1 -> selecNotChangeDual (i1::Double) (snm::SNModel)
        prop "Arbitrary SNModel isn't affected by first of two consecutive selec operations" $ do
            \snm i1 i2 -> consecutiveSelec (snm::SNModel) (i1::Double) (i2::Double)
        prop "Arbitrary SNModel doesn't change with Infl after a Selec 1 (except for Infl 0)" $ do
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
        prop "Arbitrary SNModel isn't affected by SelecVar tau1 if a SelecVar tau2 is applied after (with tau2>=tau1)" $ do
            \snm i1 i2 -> variantSelecGrowingTau (i1::Double) (i2::Double)  (snm::SNModel)
        prop "Variant Infl operation leaves relations of arbitrary SNModel unchanged" $ do
            \snm i1 -> inflVarNotChangeRel (i1::Double) (snm::SNModel)
        prop "Variant Selec operation leaves positions of agents of arbitrary SNModel unchanged" $ do
            \snm i1 -> selecVarNotChangeDual (i1::Double) (snm::SNModel)
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

