module Main where


import Test.Hspec
import ExplicitSpec

main :: IO ()
main = hspec $ do
    describe "Implementation" ExplicitSpec.spec