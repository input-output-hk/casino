{-# LANGUAGE NoImplicitPrelude #-}
module Crypto.Poker.Ledger
    ( Ledger
    , empty
    , append
    , satisfy
    , find
    ) where

import Foundation hiding (find)
import qualified Foundation as F

-- | This record the state of a game as the protocol progress
--
-- No duplicate operations should be added to the ledger, otherwise
-- it will not be possible to use the search functions properly
data Ledger a = Ledger
    { ops :: [a] -- TODO replace by a append friendly structure
    }

-- | The empty ledger
empty :: Ledger a
empty = Ledger []

-- | Append an operation to the ledger and return the new ledger
append :: (Show a, Eq a) => a -> Ledger a -> Ledger a
append a ledger
    | hasDup    = error "DUPLICATED STUFF"
    | otherwise = ledger { ops = ops ledger <> [a] }
  where
    hasDup = maybe False (const True) $ F.find (== a) (ops ledger)

-- | Check if any operation in the ledger satisfy
-- the predicate
satisfy :: (a -> Bool) -> Ledger a -> Bool
satisfy predicate ledger = any predicate (ops ledger)

-- | Try to find an operation that satisfy the predicate
find :: (a -> Bool) -> Ledger a -> Maybe a
find predicate ledger = F.find predicate (ops ledger)
