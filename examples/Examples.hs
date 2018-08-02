module Main (main) where

import qualified BiSTLC
import qualified SystemF

import Test.Tasty           (testGroup, defaultMain)

main :: IO ()
main = defaultMain $ testGroup "Examples"
    [ BiSTLC.tests
    , SystemF.tests
    ]
