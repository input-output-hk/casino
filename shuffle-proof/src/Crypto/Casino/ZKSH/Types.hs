{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
module Crypto.Casino.ZKSH.Types
    ( H
    , Z
    , UnShuffled(..)
    , Shuffled(..)
    , KnownIntNat
    , ProofDimensions
    , Verify(..)
    , verifyResult
    , verifyResultD
    , assertResult
    , Challenge(..)
    , CHash(..)
    , cHashInit
    ) where

import           Basement.Nat
import           Basement.Compat.CallStack
import           Data.Word (Word8)
import           Crypto.Hash (SHA256, hashUpdate, hashInit)
import qualified Crypto.Hash as Hash
import qualified Data.ByteArray as BA (singleton, Bytes)
import           Crypto.Casino.Primitives.ECC
import           Crypto.Casino.Primitives.Matrix (DimensionsValid )
import           Crypto.Casino.Primitives.Commitment ( Commitment, commitmentToPoint, CommitmentKey, commitmentsKeyH, commitmentsKeyGs )
import           Crypto.Casino.Primitives.TEG ( Ciphertext, ciphertextToPoints )
import           Control.DeepSeq
import           GHC.Generics (Generic)
import           Data.List (intercalate, foldl')
import qualified Basement.Sized.List as ListN
import qualified Crypto.Casino.Primitives.Matrix as Matrix

type H = Point
type Z = Scalar

-- | Unshuffled a
newtype UnShuffled a = UnShuffled { unUnShuffled :: a }
    deriving (Show,Eq,Generic)

-- | Shuffled & Randomized ciphertexts
newtype Shuffled a = Shuffled { unShuffled :: a }
    deriving (Show,Eq,Generic)

instance Functor UnShuffled where
    fmap f = UnShuffled . f . unUnShuffled

instance Functor Shuffled where
    fmap f = Shuffled . f . unShuffled

instance NFData a => NFData (UnShuffled a)
instance NFData a => NFData (Shuffled a)

data Verify a where
    (:==:) :: (Show a, Eq a) => String -> a -> a -> Verify Bool
    (:&&:) :: String -> Verify Bool -> Verify Bool -> Verify Bool
    VerifyAnds :: String -> [Verify Bool] -> Verify Bool

verifyResult :: Verify Bool -> Bool
verifyResult ((:==:) _ a b) = a == b
verifyResult ((:&&:) _ a b) = verifyResult a && verifyResult b
verifyResult (VerifyAnds _ l) = and $ map verifyResult l

verifyResultD :: Verify Bool -> [String]
verifyResultD ((:==:) s a b) = if a == b then [] else [s ++ " =>  a=" ++ show a ++ " b=" ++ show b]
verifyResultD ((:&&:) s a b) = if verifyResultD a == [] && verifyResultD b == [] then [] else prefix s (verifyResultD a) ++ prefix s (verifyResultD b)
verifyResultD (VerifyAnds s l) = concatMap (prefix s . verifyResultD) l

prefix :: String -> [String] -> [String]
prefix s l = map (\x -> s ++ " -> " ++ x) l

assertResult :: HasCallStack => Verify Bool -> Bool
assertResult v = case verifyResultD v of
    [] -> True
    l  -> error (intercalate "\n" l)

type KnownIntNat a = (KnownNat a, NatWithinBound Int a)

-- in the paper o is called capital N
--
-- many of the constraints are redundant, but GHC need exact match
-- and cannot work out commutativity or associativity rules, or
-- simple logical consequences
type ProofDimensions m n o =
    ( (m * n) ~ o, (n * m) ~ o
    , 1 <= n , 1 <= m , 1 <= (m+m), 1 <= (m+m+1), 1 <= (m-1), (m-1) <= m
    , KnownIntNat m, KnownIntNat n, KnownIntNat o, KnownIntNat (m+m), KnownIntNat (m-1)
    , KnownIntNat (m+1)
    , KnownIntNat (m-1)
    , KnownIntNat ((m+m)+1)
    , DimensionsValid m n
    , DimensionsValid (m+1) n
    )

class CHash a where
    cHashUpdate :: a -> Hash.Context SHA256 -> Hash.Context SHA256
instance CHash Point where
    cHashUpdate p c = hashUpdate c (pointToBinary p)
instance CHash Scalar where
    cHashUpdate s c = hashUpdate c (scalarToBinary s)
instance CHash (CommitmentKey n) where
    cHashUpdate ck = cHashUpdate (commitmentsKeyH ck)
                   . cHashUpdate (commitmentsKeyGs ck)
instance CHash (Commitment n) where
    cHashUpdate com = cHashUpdate (commitmentToPoint com)
instance CHash Ciphertext where
    cHashUpdate c = cHashUpdate a . cHashUpdate b
      where (a,b) = ciphertextToPoints c
instance CHash Word8 where
    cHashUpdate w c = hashUpdate c (BA.singleton w :: BA.Bytes)

instance CHash a => CHash [a] where
    cHashUpdate l c = foldl' (flip cHashUpdate) c l
instance CHash a => CHash (ListN.ListN n a) where
    cHashUpdate l c = ListN.foldl' (flip cHashUpdate) c l
instance CHash a => CHash (Matrix.Matrix m n a) where
    cHashUpdate m c = ListN.foldl' (flip cHashUpdate) c (Matrix.toList m)
instance CHash a => CHash (Shuffled a) where
    cHashUpdate m = cHashUpdate (unShuffled m)
instance CHash a => CHash (UnShuffled a) where
    cHashUpdate m = cHashUpdate (unUnShuffled m)

cHashInit :: Hash.Context SHA256
cHashInit = hashInit

class Challenge a where
    challenge :: a -> Scalar
