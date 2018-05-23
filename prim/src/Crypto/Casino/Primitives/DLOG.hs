{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveGeneric #-}
module Crypto.Casino.Primitives.DLOG
    where

import           Control.DeepSeq
import           Crypto.Casino.Primitives.ECC
import           Data.ByteString (ByteString)
import           GHC.Generics

data DLOG = DLOG
    { dlog_g :: !Point -- ^ g parameter
    , dlog_x :: !Point -- ^ x parameter where x = g^alpha
    } deriving (Show,Eq,Generic)

instance NFData DLOG

newtype Challenge = Challenge ByteString
    deriving (Show,Eq,NFData)

-- | The generated proof
data Proof = Proof
    { proof_e :: !Challenge
    , proof_z :: !Scalar
    } deriving (Show,Eq,Generic)

instance NFData Proof

-- | Generate a proof for g^alpha = x, DLOG(g,x)
generate :: Scalar -- ^ random value
         -> Scalar -- ^ alpha
         -> DLOG   -- ^ DLOG parameters to generate from
         -> Proof
generate w alpha (DLOG g x) = Proof (Challenge e) z
  where
    a = g .* w
    e = hashPoints [g,x,a]
    z = w #+ (alpha #* keyFromBytes e)

-- | Verify a proof
verify :: DLOG  -- ^ DLOG parameter used to verify
       -> Proof -- ^ the proof to verify
       -> Bool
verify (DLOG g x) (Proof (Challenge e) z) =
    e == hashPoints [g,x,a]
  where
    a = (g .* z) .- (x .* keyFromBytes e)
