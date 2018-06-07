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
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
import           Foundation.Check
import           Data.Proxy
import           Data.Type.Equality
import           Unsafe.Coerce (unsafeCoerce)
import           GHC.Generics
import           Control.DeepSeq
import           Crypto.Random
import           Crypto.Casino.Primitives.SSize
import           Crypto.Casino.Primitives.HelperListN (rewriteListN_P1M1)
import           Crypto.Casino.Primitives.ECC
import qualified Crypto.Casino.Primitives.DLOG as DLOG
import           Crypto.Casino.Primitives.TEG (Random)
import           Crypto.Casino.Primitives.Matrix

type H = Point

data KeyPart = KeyPart
    { keyPartPoint :: Point
    , keyPartProof :: DLOG.Proof
    } deriving (Show,Eq,Generic)

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

keyPartGenerate :: MonadRandom randomly => randomly KeyPart
keyPartGenerate = do
    w <- keyGenerate
    k <- keyGenerate
    let point = pointFromSecret k
    let proof = DLOG.generate w k (DLOG.DLOG curveGenerator point)
    pure $ KeyPart point proof

keyPartCombine :: forall n . ListN (n+1) KeyPart -> Maybe (CommitmentKey n)
keyPartCombine l
    | proofsValid = Just $ CommitmentKey
        { commitmentsKeyGs = rewriteListN_P1M1 $ ListN.map keyPartPoint gs
        , commitmentsKeyH  = keyPartPoint $ h
        }
    | otherwise = Nothing
  where
    proofsValid = and $ ListN.unListN $ ListN.map verifyOneProof l
    verifyOneProof keyPart = DLOG.verify (DLOG.DLOG curveGenerator $ keyPartPoint keyPart) (keyPartProof keyPart)
    (h, gs) = case x_lessequal_n_plus_x @1 @n of
                Refl -> (ListN.head l, ListN.tail l)

x_lessequal_n_plus_x :: forall x n . ('True :~: (x <=? (n + x)))
x_lessequal_n_plus_x = unsafeCoerce Refl

keyNew :: forall n randomly . ( MonadRandom randomly, KnownNat n, NatWithinBound Int n)
       => randomly (CommitmentKey n)
keyNew = CommitmentKey <$> ListN.replicateM pointGenerate
                       <*> pointGenerate
  where pointGenerate = pointFromSecret <$> keyGenerate

keyAdd :: CommitmentKey n -> CommitmentKey n -> CommitmentKey n
keyAdd ck1 ck2 = CommitmentKey
    { commitmentsKeyGs = ListN.zipWith (.+) (commitmentsKeyGs ck1) (commitmentsKeyGs ck2)
    , commitmentsKeyH  = commitmentsKeyH ck1 .+ commitmentsKeyH ck2
    }

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
