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
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE UndecidableInstances #-}
module Crypto.Casino.ZKSH.MultiExponentiation
    ( Proof(..)
    , Stmt(..)
    , Witness(..)
    , stmtFromWitness
    , proove
    , verify
    ) where

import           Basement.Nat
import           GHC.Exts
import           Basement.Types.OffsetSize
import           Data.Proxy
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
import           Control.DeepSeq
import           Crypto.Random
import           Crypto.Casino.Primitives.ECC
import           Crypto.Casino.Primitives.SSize
import           Crypto.Casino.Primitives.Matrix (Matrix, toRows)
import qualified Crypto.Casino.Primitives.Matrix as Matrix
import           Crypto.Casino.Primitives.HelperListN
import           Crypto.Casino.Primitives.Commitment
import           Crypto.Casino.Primitives.TEG (Random)
import qualified Crypto.Casino.Primitives.TEG as TEG
import           Prelude hiding (product)

import           Crypto.Casino.ZKSH.Types
import           Crypto.Casino.ZKSH.Operations

import           GHC.Generics (Generic)

data Proof (m :: Nat) (n :: Nat) = Proof
    {
    -- initial message
      mep_Ca0  :: Commitment n
    , mep_Cb   :: ListN (m+m) (Commitment n)
    , mep_E    :: ListN (m+m) TEG.Ciphertext
    -- answer after challenge
    , mep_avec :: ListN n Scalar
    , mep_r    :: Scalar
    , mep_b    :: Scalar
    , mep_s    :: Scalar
    , mep_tau  :: Scalar
    } deriving (Show, Eq, Generic)

instance SSize (Proof m n) where
    type SizePoints (Proof m n) =
        SizePoints (Commitment n) +
        SizePoints (ListN (m+m) (Commitment n)) +
        SizePoints (ListN (m+m) TEG.Ciphertext) +
        SizePoints (ListN n Scalar) +
        SizePoints Scalar +
        SizePoints Scalar +
        SizePoints Scalar +
        SizePoints Scalar
    type SizeScalar (Proof m n) =
        SizeScalar (Commitment n) +
        SizeScalar (ListN (m+m) (Commitment n)) +
        SizeScalar (ListN (m+m) TEG.Ciphertext) +
        SizeScalar (ListN n Scalar) +
        SizeScalar Scalar +
        SizeScalar Scalar +
        SizeScalar Scalar +
        SizeScalar Scalar

instance NFData (Proof m n)

data Stmt (m :: Nat) (n :: Nat) = Stmt
    { stmt_C    :: Shuffled (Matrix m n TEG.Ciphertext) -- ^ shuffled ciphertext
    , stmt_csum :: TEG.Ciphertext
    , stmt_Ca   :: ListN m (Commitment n)
    } deriving (Show, Eq, Generic)

instance NFData (Stmt m n)

instance Challenge (Stmt m n) where
    challenge (Stmt c csum ca) =
        hashFinalizeScalar $ cHashUpdate ca
                           $ cHashUpdate csum
                           $ cHashUpdate c
                           $ cHashInit

data Witness m n = Witness
    { witness_A   :: Matrix m n Scalar
    , witness_r   :: ListN m Random
    , witness_rho :: Random
    } deriving (Show,Eq,Generic)

stmtFromWitness :: forall m n o . ProofDimensions m n o
                => TEG.JointPublicKey
                -> CommitmentKey n
                -> Shuffled (Matrix m n TEG.Ciphertext)
                -> Witness m n
                -> Stmt m n
stmtFromWitness pk ck ciphertexts (Witness a rs rho) =
    Stmt { stmt_C    = ciphertexts
         , stmt_csum = TEG.reEncrypter pk rho `TEG.ciphertextMul`
                       (TEG.ciphertextProduct
                        $ ListN.unListN
                        $ ListN.zipWith TEG.productCiphertextExponentiate (Matrix.toRows (unShuffled ciphertexts)) (Matrix.toRows a))
         , stmt_Ca   = commitmentMatrix ck a rs
         }

proove :: forall m n o k randomly
        . ( MonadRandom randomly
          , ProofDimensions m n o
          , KnownNat k
          , NatWithinBound Int k
          , k ~ (m + m))
       => TEG.JointPublicKey
       -> CommitmentKey n
       -> Shuffled (Matrix m n TEG.Ciphertext)
       -> Witness m n
       -> randomly (Proof m n)
proove pk ck ciphertexts@(Shuffled rawCiphertexts) witness@(Witness a rs rho) = do
    a0  <- randoms @n
    r0  <- keyGenerate
    b   <- updateAtM @m (const $ keyFromNum 0) <$> randoms @k
    s   <- updateAtM @m (const $ keyFromNum 0) <$> randoms @k
    tau <- updateAtM @m (const rho) <$> randoms @k

    -- initial message c_A0, c_B_k, E_k
    let ca0 = commitment ck a0 r0
        cb  = ListN.zipWith (\bi si -> commitment ck (extendSingletonWithZero bi) si) b s
        -- create E_k's
        e1 :: ListN k TEG.Ciphertext
        e1  = ListN.zipWith (\bi ti -> TEG.encryptionWith pk (pointFromSecret bi) ti) b tau
        e2 :: ListN k TEG.Ciphertext
        e2  = flip ListN.map range $ \k ->
                    let m = natValInt (Proxy @m)
                        idx = [ (i,j) | i <- [1..m], j <- [0..m], j == (k-m)+i ]
                        single (i, j) =
                            let ci = toRows rawCiphertexts `ListN.index` Offset (i - 1)
                                aj | j == 0    = a0
                                   | otherwise = toRows a `ListN.index` Offset (j - 1)
                             in TEG.productCiphertextExponentiate ci aj
                     in TEG.ciphertextProduct $ map single idx
        e  = ListN.zipWith TEG.ciphertextMul e1 e2


    --when (e `ListN.index` (Offset $ natValInt (Proxy @m)) /= stmt_csum stmt) $
    --  error ("FAILED\ne1= " ++ show e1 ++ "\ne2= " ++ show e2 ++ "\ne = " ++ show e ++ "\nC = " ++ show (stmt_csum stmt))

    let vx = exponentsOfX @m x

    let aSum = a0 |+| (Matrix.toCols a |*| vx)
        rSum = r0 #+ (innerProduct rs vx)
        bSum = sumScalarN $ ListN.zipWith (#*) (exponentsOfXFrom1 x) b
        sSum = sumScalarN $ ListN.zipWith (#*) (exponentsOfXFrom1 x) s
        tauSum = sumScalarN $ ListN.zipWith (#*) (exponentsOfXFrom1 x) tau

    pure $ Proof { mep_Ca0  = ca0
                 , mep_Cb   = cb
                 , mep_E    = e
                 , mep_avec = aSum
                 , mep_r    = rSum
                 , mep_b    = bSum
                 , mep_s    = sSum
                 , mep_tau  = tauSum
                 }
  where
    stmt = stmtFromWitness pk ck ciphertexts witness
    x = challenge stmt


verify :: forall m n o . ProofDimensions m n o
       => TEG.JointPublicKey
       -> CommitmentKey n
       -> Proof m n
       -> Stmt m n
       -> Verify Bool
verify pk ck proof stmt =
    VerifyAnds (fromList ("multi exponentiation m=" ++ show m ++ " n=" ++ show n))
        [ (:==:) "C_Bm == com(0;0)"
            (ListN.index (mep_Cb proof) (Offset m))
            (commitment ck (ListN.replicate $ keyFromNum 0) (keyFromNum 0))
        , (:==:) "Em == C"
            (ListN.index (mep_E proof) (Offset $ m))
            (stmt_csum stmt)
        , (:==:) "ca0 * ca^x == com(a;r)"
            (mep_Ca0 proof `commitmentMul` (commitmentsExponentiate (stmt_Ca stmt) (exponentsOfX x)))
            (commitment ck (mep_avec proof) (mep_r proof))
        , (:==:) "Cb0 * prod(C_bk^(x^k)) == com(b;s)"
            (commitmentProd $ ListN.zipWith commitmentExponentiate (mep_Cb proof) (exponentsOfXFrom1 x))
            (commitment ck (extendSingletonWithZero $ mep_b proof) (mep_s proof))
        , (:==:) "E0 * prod(E_k^(x^k)) == E(G^b;r) * prod(C_i ^ (x^(m-i) * a))"
            (TEG.productCiphertextExponentiate (mep_E proof) (exponentsOfXFrom1 x))
            (TEG.encryptionWith pk (pointFromSecret $ mep_b proof) (mep_tau proof) `TEG.ciphertextMul`
             (TEG.ciphertextProduct $ ListN.unListN
                                    $ ListN.zipWith TEG.productCiphertextExponentiate
                                                    (toRows $ unShuffled $ stmt_C stmt)
                                                    (ListN.zipWith (*|) (ListN.reverse $ exponentsOfXFrom1 x) (ListN.replicate $ mep_avec proof)))
            )
        ]
  where
    m = natValInt (Proxy @m)
    n = natValInt (Proxy @n)
    x = challenge stmt

updateAtM :: forall m k a . (NatWithinBound Int m, NatWithinBound Int k, KnownNat k, KnownNat m)
          => (a -> a) -> ListN k a -> ListN k a
updateAtM f = ListN.updateAt (Offset $ natValInt (Proxy @m)) f
