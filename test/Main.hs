module Main (main) where

import Test.Tasty

import qualified Test.NoThunks.Class

tests :: TestTree
tests = testGroup "Tests" [
      Test.NoThunks.Class.tests
    ]

main :: IO ()
main = defaultMain tests
