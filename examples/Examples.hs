module Main (main) where

import qualified BiSTLC
import qualified BiSTLC2
import qualified BiSTLC3
import qualified SystemF

import Test.Tasty           (testGroup, defaultMain)

main :: IO ()
main = defaultMain $ testGroup "Examples"
    [ BiSTLC.tests
    , BiSTLC2.tests
    , BiSTLC3.tests
    , SystemF.tests
    ]
