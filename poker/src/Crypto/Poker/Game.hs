-- Represent a Generic DSL for game like operation
-- with a built-in interruptible API.
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Crypto.Poker.Game where

import qualified Crypto.Casino.Primitives.TEG as TEG (PublicBroadcast)
import qualified Crypto.Casino.Primitives.SIG as SIG (VerifyKey)
import           Basement.Imports
import           Basement.Nat

type PlayerNumber = Natural -- order of players

data Event operation = Event
    { eventGetPlayerNumber :: PlayerNumber
    , eventGetOperation    :: operation
    }
    deriving (Show,Eq)

isEventFromPlayer :: PlayerNumber -> Event operation -> Bool
isEventFromPlayer p1 (Event p2 _) = p1 == p2

-- | This represent a DSL of all possible operations.
data Result operation gameSt (n :: Nat) result =
      Failed    String
    | Ok        (gameSt n) result
    | Broadcast (gameSt n) operation (Resume operation gameSt n result ())
    | FSC       (gameSt n) SIG.VerifyKey TEG.PublicBroadcast (Resume operation gameSt n result PlayerNumber)
    | Input     (gameSt n) String (Resume operation gameSt n result String)
    | Next      (gameSt n) String (Resume operation gameSt n result (Event operation))
    | Debug     (gameSt n) String (Resume operation gameSt n result ())

type Resume operation gameState n result param = gameState n -> param -> Result operation gameState n result

instance Functor (Result operation gameSt n) where
    fmap f r = case r of
        Failed err        -> Failed err
        Ok rest a         -> Ok rest (f a)
        Broadcast st op k -> Broadcast st op (fmapResume f k)
        FSC st vrf pb k   -> FSC st vrf pb (fmapResume f k)
        Input st s k      -> Input st s (fmapResume f k)
        Next st s k       -> Next st s (fmapResume f k)
        Debug st s k      -> Debug st s (fmapResume f k)
      where
        fmapResume fct k = (fmap fct .) . k

type Failure operation gameSt n result         = gameSt n -> String -> Result operation gameSt n result
type Success operation gameSt n result' result = gameSt n -> result' -> Result operation gameSt n result
