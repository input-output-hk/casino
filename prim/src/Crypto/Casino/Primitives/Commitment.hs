{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
module Crypto.Casino.Primitives.Commitment
    where

import           Basement.Nat
import           Foundation.List.ListN (ListN)
import qualified Foundation.List.ListN as ListN
import           Foundation.Check
import           Data.Proxy
import           GHC.Generics
import           Control.DeepSeq
import           Crypto.Random
import           Crypto.Casino.Primitives.SSize
import           Crypto.Casino.Primitives.ECC
import           Crypto.Casino.Primitives.TEG (Random)
import           Crypto.Casino.Primitives.Matrix

type H = Point

data CommitmentKey (n :: Nat) = CommitmentKey
    { commitmentsKeyGs :: ListN n Point
    , commitmentsKeyH  :: H
    } deriving (Show,Eq,Generic)

-- | Generalized Pedersen commitment to N values
newtype Commitment (n :: Nat) = Commitment { commitmentToPoint :: Point }
    deriving (Eq,Generic)

instance SSize (Commitment n) where
    type SizePoints (Commitment n) = (n + 1)
    type SizeScalar (Commitment n) = 0

instance NFData (Commitment n)

instance (KnownNat n) => Show (Commitment (n :: Nat)) where
    show (Commitment p) = "Commitment " ++ show (natVal (Proxy :: Proxy n)) ++ " " ++ show p

instance (KnownNat n, NatWithinBound Int n) => Arbitrary (CommitmentKey n) where
    arbitrary = arbitrary >>= \drg -> pure $ fst (withDRG (drgNewTest drg) keyNew)

keyNew :: forall n randomly . ( MonadRandom randomly, KnownNat n, NatWithinBound Int n)
       => randomly (CommitmentKey n)
keyNew = CommitmentKey <$> ListN.replicateM pointGenerate
                       <*> pointGenerate
  where pointGenerate = pointFromSecret <$> keyGenerate

-- | Compute COM_ck( {a1, ... , an} , r )
commitment :: CommitmentKey n -> ListN n Scalar -> Random -> Commitment n
commitment ck as r =
    Commitment ((commitmentsKeyH ck .* r) .+ foldl (.+) pointIdentity l)
  where
    l = ListN.unListN $ ListN.zipWith (.*) (commitmentsKeyGs ck) as

-- | Mul 2 commitments together
--
-- COM_ck(â, r) * COM_ck(ê, s) = COM_ck(â + ê , r + s)
commitmentAdd :: Commitment n -> Commitment n -> Commitment n
commitmentAdd (Commitment a) (Commitment b) = Commitment (a .+ b)
{-# DEPRECATED commitmentAdd "use commitmentMul" #-}

commitmentMul :: Commitment n -> Commitment n -> Commitment n
commitmentMul (Commitment a) (Commitment b) = Commitment (a .+ b)

commitmentExponentiate :: Commitment n -> Scalar -> Commitment n
commitmentExponentiate (Commitment a) s = Commitment (a .* s)

commitmentsExponentiate :: ListN n (Commitment x) -> ListN n Scalar -> Commitment x
commitmentsExponentiate (ListN.map commitmentToPoint -> l) s =
    Commitment $ ListN.foldl (.+) pointIdentity $ ListN.zipWith (.*) l s

-- | same as 'commitment' but linked to a matrix
commitmentMatrix :: DimensionsValid m n
                 => CommitmentKey n
                 -> Matrix m n Scalar
                 -> ListN m Random
                 -> ListN m (Commitment n)
commitmentMatrix ck ls rs = ListN.zipWith (commitment ck) (toRows ls) rs

commitmentProd :: 1 <= n => ListN n (Commitment x) -> Commitment x
commitmentProd = ListN.foldl1' commitmentAdd
