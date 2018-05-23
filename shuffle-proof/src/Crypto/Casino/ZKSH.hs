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
module Crypto.Casino.ZKSH
    ( shuffleProve
    , shuffleVerify
    , ProofDimensions
    , ShuffleProof(..)
    , ShuffleStmt(..)
    , Shuffled(..)
    , UnShuffled(..)
    , Witness(..)
    , stmtFromWitness
    , verifyResult
    , assertResult
    ) where

import           Basement.Nat
import           Data.Word
import           Foundation.List.ListN (ListN)
import qualified Foundation.List.ListN as ListN
import           Control.DeepSeq
import           GHC.Generics (Generic)
import           Crypto.Random
import           Crypto.Casino.Primitives.Permutation
import qualified Crypto.Casino.Primitives.Permutation as Permut
import           Crypto.Casino.Primitives.ECC
import qualified Crypto.Casino.Primitives.Matrix as Matrix
import           Crypto.Casino.Primitives.Commitment
import qualified Crypto.Casino.Primitives.TEG as TEG
import           Prelude hiding (product)

import           Crypto.Casino.Primitives.SSize
import           Crypto.Casino.ZKSH.Types
import           Crypto.Casino.ZKSH.Operations
import qualified Crypto.Casino.ZKSH.MultiExponentiation as ME
import qualified Crypto.Casino.ZKSH.Product as Prod

data ShuffleProof (m :: Nat) (n :: Nat) = ShuffleProof
    { shuffleProofPermutations       :: ListN m (Commitment n) -- ^ paper's ca
    , shuffleProofExponentiatedPerms :: ListN m (Commitment n) -- ^ paper's cb
    , shuffleProofME                 :: ME.Proof m n
    , shuffleProofProduct            :: Prod.Proof m n
    } deriving (Show, Eq, Generic)

instance SSize (ShuffleProof m n) where
    type SizePoints (ShuffleProof m n) =
        SizePoints (ListN m (Commitment n)) +
        SizePoints (ListN m (Commitment n)) +
        SizePoints (ME.Proof m n) +
        SizePoints (Prod.Proof m n)
    type SizeScalar (ShuffleProof m n) =
        SizeScalar (ListN m (Commitment n)) +
        SizeScalar (ListN m (Commitment n)) +
        SizeScalar (ME.Proof m n) +
        SizeScalar (Prod.Proof m n)

instance NFData (ShuffleProof m n)

data ShuffleStmt (o :: Nat) = ShuffleStmt
    { shuffleStmtC  :: UnShuffled (ListN o TEG.Ciphertext) -- ^ original ciphertexts
    , shuffleStmtC' :: Shuffled (ListN o TEG.Ciphertext) -- ^ shuffled ciphertexts
    } deriving (Show, Eq, Generic)

newtype ShuffleStmtWithX (o :: Nat) = ShuffleStmtWithX (ShuffleStmt o)
    deriving (Show, Eq, Generic)

newtype ShuffleStmtWithXY (o :: Nat) = ShuffleStmtWithXY (ShuffleStmt o)
    deriving (Show, Eq, Generic)

instance Challenge (ShuffleStmt o) where
    challenge (ShuffleStmt a b) =
        hashFinalizeScalar $ cHashUpdate b
                           $ cHashUpdate a
                           $ cHashUpdate (0 :: Word8)
                           $ cHashInit

instance Challenge (ShuffleStmtWithX o) where
    challenge (ShuffleStmtWithX stmt@(ShuffleStmt a b)) =
        hashFinalizeScalar $ cHashUpdate b
                           $ cHashUpdate a
                           $ cHashUpdate (1 :: Word8)
                           $ cHashInit

instance Challenge (ShuffleStmtWithXY o) where
    challenge (ShuffleStmtWithXY stmt@(ShuffleStmt a b)) =
        hashFinalizeScalar $ cHashUpdate b
                           $ cHashUpdate a
                           $ cHashUpdate (2 :: Word8)
                           $ cHashInit

data Witness o = Witness
    { w_perm :: Permutation o      -- ^ The permutation used
    , w_rhos :: ListN o TEG.Random -- ^ Ciphertext Randomize Value use for re-encryption
    } deriving (Show,Eq,Generic)

instance NFData (Witness o)

runShuffle :: (KnownNat o, NatWithinBound Int o)
           => TEG.JointPublicKey
           -> Witness o
           -> UnShuffled (ListN o TEG.Ciphertext)
           -> Shuffled (ListN o TEG.Ciphertext)
runShuffle pk (Witness perm rhos) (UnShuffled ciphers) =
    Shuffled $ ListN.zipWith TEG.ciphertextMul encrypter shuffled
  where
    encrypter = ListN.map (TEG.reEncrypter pk) rhos
    shuffled = Permut.apply perm ciphers

stmtFromWitness :: (KnownNat o, NatWithinBound Int o)
                => TEG.JointPublicKey
                -> Witness o                           -- ^ permutation & reencryption witness
                -> UnShuffled (ListN o TEG.Ciphertext) -- ^ original ciphertexts (non shuffled, non re-encrypted)
                -> ShuffleStmt o
stmtFromWitness pk witness ciphers =
    ShuffleStmt ciphers (runShuffle pk witness ciphers)

shuffleProve :: forall m n o randomly
              . (MonadRandom randomly, ProofDimensions m n o)
             => TEG.JointPublicKey
             -> CommitmentKey n
             -> Witness o
             -> UnShuffled (ListN o TEG.Ciphertext) -- ^ the original ciphertext
             -> randomly (ShuffleProof m n)
shuffleProve pk ck w@(Witness perm randomizers) original = do
    let stmt = stmtFromWitness pk w original
        ciphertexts = shuffleStmtC' stmt

    r <- ListN.replicateM @m keyGenerate
    s <- ListN.replicateM @m keyGenerate

    let x = challenge stmt

    -- b = { x ^ perm(i) } i=1..N
    let b = Permut.export (\i -> x #^ i) perm :: ListN.ListN o Scalar

    let ca = commitmentMatrix ck (Matrix.fromList a) r
        cb = commitmentMatrix ck (Matrix.fromList b) s

    let y = challenge (ShuffleStmtWithX stmt)
        z = challenge (ShuffleStmtWithXY stmt)

    let -- vz = ListN.replicate (keyInverse z) :: ListN n Scalar
        -- cd = (commitmentsToPoints ca |.*| y) |.+| commitmentsToPoints cb
        t = (y *| r) |+| s :: ListN m Scalar
        d = (y *| a) |+| b :: ListN o Scalar
        -- cmz = commitmentMatrix ck undefined t
        dmz = ListN.map (\di -> di #- z) d
        -- prod = vectorProduct dmz
        rho = innerProduct (vectorNegate randomizers) b

    mep <- ME.proove pk ck (Matrix.fromList `fmap` ciphertexts)
                           (ME.Witness (Matrix.fromList b) s rho)
    p <- Prod.proove ck (Prod.Witness (Matrix.fromList dmz) t)

    pure $ ShuffleProof
        { shuffleProofPermutations       = ca
        , shuffleProofExponentiatedPerms = cb
        , shuffleProofME                 = mep
        , shuffleProofProduct            = p
        }
  where
    -- a = { perm(i) } i=1..N
    a :: ListN.ListN o Scalar
    a = Permut.export (keyFromNum . toInteger) perm

shuffleVerify :: forall m n o . (ProofDimensions m n o)
              => TEG.JointPublicKey
              -> CommitmentKey n
              -> ShuffleProof m n
              -> ShuffleStmt o
              -> Verify Bool
shuffleVerify pk ck proof stmt =
    VerifyAnds "shuffle"
        [ ME.verify @m @n @o pk ck (shuffleProofME proof) meStatement
        , Prod.verify ck (shuffleProofProduct proof) prodStatement
        ]
  where
    x = challenge stmt
    y = challenge (ShuffleStmtWithX stmt)
    z = challenge (ShuffleStmtWithXY stmt)
    negZ = keyNegate z

    -- make the multi exponentiation statement
    meStatement = ME.Stmt { ME.stmt_C    = fmap Matrix.fromList $ shuffleStmtC' stmt
                          , ME.stmt_csum = TEG.bilinearMap (unUnShuffled $ shuffleStmtC stmt) (exponentsOfX x)
                          , ME.stmt_Ca   = shuffleProofExponentiatedPerms proof
                          }

    -- make the product statement
    prodStatement = Prod.Statement { Prod.stmt_ca = prodCa , Prod.stmt_b = prodSum }

    -- calculate Cd * C_-z where Cd = Ca ^ y * cb and C_-z is C(-z, .., -z; 0)
    prodCa :: ListN m (Commitment n)
    prodCa = ListN.zipWith commitmentMul cd cmz
      where cd = ListN.zipWith commitmentMul
                               (ListN.map (\c -> c `commitmentExponentiate` y) $ shuffleProofPermutations proof)
                               (shuffleProofExponentiatedPerms proof)
            cmz = commitmentMatrix ck (Matrix.fromList $ ListN.replicate negZ)
                                      (ListN.replicate $ keyFromNum 0)

    -- calculate product from 1 to N of y*i + x^i - z
    -- which is used to verify the product single value
    prodSum :: Scalar
    prodSum = vectorProduct
            $ ListN.zipWith (#+) (ListN.create (\i -> y #* keyFromNum (fromIntegral i+1)))
            $ ListN.zipWith (#+) (exponentsOfX x)
            $ ListN.replicate @o negZ

{-
commitmentsToPoints :: ListN n (Commitment x) -> ListN n Point
commitmentsToPoints = ListN.map commitmentToPoint
-}
