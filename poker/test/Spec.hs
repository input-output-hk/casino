{-# LANGUAGE OverloadedStrings #-}
module Main where

import Foundation.Check
import Foundation.Check.Main

import Crypto.Poker.Tests

main :: IO ()
main = defaultMain $ Group "poker"
    [ proofs
    , permutationProofs
    ]
