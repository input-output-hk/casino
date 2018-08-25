{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies, TypeOperators, TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Crypto.Poker.Tests
    ( proofs
    , permutationProofs
    ) where

import           Data.Proxy
import           Data.Word
import           Basement.Nat
import           Basement.From
import           Basement.Bounded
import           Basement.Imports hiding (Generic(from), fst)
import           Basement.Types.OffsetSize
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
-- import qualified Basement.Sized.List as ListN
import           Foundation.Check
import qualified Crypto.Casino.Primitives.Permutation as Permutation
import qualified Crypto.Casino.Primitives.TEG as TEG
import qualified Crypto.Casino.Primitives.ECC as ECC
import           Crypto.Casino.ZKSH
import           Crypto.Casino.ZKSH.Types
import qualified Crypto.Casino.ZKSH.Product as Prod
import           Crypto.Casino.ZKSH.Operations (productScalar)
import           Crypto.Casino.Primitives.Commitment
--import           Crypto.Casino.Primitives.Matrix (Matrix)
--import qualified Crypto.Casino.Primitives.Matrix as Matrix
import           Crypto.Random
import           Crypto.Poker.Card
import qualified Crypto.Poker.Hand as H
import           Foundation
import           Foundation.Collection

--instance (NatWithinBound Int n, KnownNat n, Arbitrary a) => Arbitrary (ListN n a) where
--    arbitrary = ListN.replicateM arbitrary
--instance KnownNat n => Arbitrary (Permutation.Permutation n) where
--    arbitrary = error "arbitrayr permutation"

newtype TestDRG = TestDRG (Word64, Word64, Word64, Word64, Word64)
    deriving (Show,Eq)

instance Arbitrary TestDRG where
    arbitrary = TestDRG `fmap` arbitrary

instance Arbitrary Suit where
    arbitrary = elements $ nonEmpty_ [minBound..maxBound]
instance Arbitrary Rank where
    arbitrary = elements $ nonEmpty_ [minBound..maxBound]
instance Arbitrary Card where
    arbitrary = Card <$> arbitrary <*> arbitrary

withTestDRG :: TestDRG -> MonadPseudoRandom ChaChaDRG a -> a
withTestDRG (TestDRG l) f = fst $ withDRG (drgNewTest l) f

proofs :: Test
proofs = Group "Poker"
    [ TEG.properties
    , Group "hand"
        [ Property "singleton" $ \c -> H.fromHand (H.toHand [c]) == [c]
        , Property "subsetOf" $ \c -> let h = H.toHand [c] in H.subsetOf h h
        , Property "onlyRank" $ \c ->
            H.onlyRank (cardRank c) (H.toHand [c]) === H.toHand [c]
        , Property "onlySuit" $ \c ->
            H.onlySuit (cardSuit c) (H.toHand [c]) === H.toHand [c]
        , Property "pair vs 3kind" $
            (H.toHand [Card Diamonds R8, Card Hearts R8] `compare` H.toHand [Card Diamonds R2, Card Hearts R2, Card Clubs R2]) === LT
        , Property "pair vs pair" $
            (H.toHand [Card Diamonds R8, Card Hearts R8] `compare` H.toHand [Card Diamonds R2, Card Hearts R2]) === GT
        ]
    , Group "commitment" [ commitmentProofs (Proxy :: Proxy 4)
                         , commitmentProofs (Proxy :: Proxy 13) ]
    , productProofs
    ]

{-
replicateEccScalar :: CountOf x -> x -> Array x
replicateEccScalar n x = replicate n x
-}

commitmentProofs :: forall n . (KnownNat n, 1 <= n, NatWithinBound Int n) => Proxy n -> Test
commitmentProofs pn = Group (show $ natVal pn)
    [ Property "mul" $ \(ck :: CommitmentKey n)
                        (l1  :: ListN n ECC.Scalar)
                        (l2  :: ListN n ECC.Scalar)
                        (r1 :: ECC.Scalar)
                        (r2 :: ECC.Scalar) ->
            let c1 = commitment ck l1 r1 `commitmentMul` commitment ck l2 r2
                c2 = commitment ck (ListN.zipWith (ECC.#+) l1 l2) (r1 ECC.#+ r2)
             in c1 === c2
    , Property "square" $ \(ck :: CommitmentKey n) l r ->
            let c1 = commitment ck l r
             in commitmentMul c1 c1 === commitmentExponentiate c1 (ECC.keyFromNum 2)
    , Property "exponentiate" $ \(ck :: CommitmentKey n) l r (n' :: Zn64 64) ->
        let n = 1 + CountOf (fromIntegral (unZn64 n'))
            c1 = commitment ck l r
            c1n = commitmentExponentiate c1 (ECC.keyFromNum $ from n)
            ln  = foldl1' (ListN.zipWith (ECC.#+)) $ nonEmpty_ (replicate n l :: Array (ListN n ECC.Scalar))
            rn  = foldl1' (ECC.#+) $ nonEmpty_ (replicate (sizeCast Proxy n) r :: Array ECC.Scalar)
         in c1n === commitment ck ln rn
    ]

permutationProofs :: Test
permutationProofs = Group "permutation"
    [ permutationsParams (Proxy :: Proxy 2) (Proxy :: Proxy 2) (Proxy :: Proxy 4)
    , permutationsParams (Proxy :: Proxy 4) (Proxy :: Proxy 4) (Proxy :: Proxy 16)
    , permutationsParams (Proxy :: Proxy 8) (Proxy :: Proxy 2) (Proxy :: Proxy 16)
    , permutationsParams (Proxy :: Proxy 2) (Proxy :: Proxy 8) (Proxy :: Proxy 16)

    , permutationsParams (Proxy :: Proxy 2) (Proxy :: Proxy 16) (Proxy :: Proxy 32)
    , permutationsParams (Proxy :: Proxy 4) (Proxy :: Proxy 8) (Proxy :: Proxy 32)
    ]
  where
    permutationsParams :: forall m n o
                        . ProofDimensions m n o
                       => Proxy m
                       -> Proxy n
                       -> Proxy o
                       -> Test
    permutationsParams _ _ _ = Property "permutation" $
        \(jpk       :: TEG.JointPublicKey)
         (ck        :: CommitmentKey n)
         (permuts   :: Permutation.Permutation o)
         (rans      :: ListN o TEG.Random)
         testDRG
         (original  :: ListN o TEG.Ciphertext) ->
            let unshuffled = UnShuffled original
                -- permuts  = Permutation.identity -- to test no permutation
                witness  = Witness permuts rans
                stmt     = stmtFromWitness jpk witness unshuffled
                proof    = withTestDRG testDRG $ shuffleProve @m @n @o jpk ck witness unshuffled
             in assertResult $ shuffleVerify @m @n @o jpk ck proof stmt

productProofs :: Test
productProofs = Group "product"
    [ Group "single-value"
        [ Property "positive-2" $ testSingleValue (Proxy :: Proxy 2)
        , Property "positive-4" $ testSingleValue (Proxy :: Proxy 4)
        ]
        {- this is disabled until the test is correct
    , Group "zero"
        [ Property "positive" $ testZero (Proxy :: Proxy 2) (Proxy :: Proxy 2)
        ]
        -}
    ]
  where
    testSingleValue :: forall n . (Prod.SingleValueConstraint n)
                    => Proxy n -> CommitmentKey n -> ListN n ECC.Scalar -> TEG.Random -> TestDRG -> Bool
    testSingleValue _ ck a r testDRG =
        let ca       = commitment ck a r
            b        = productScalar (ListN.unListN a)
            stmt     = Prod.SingleValueProductStatement ca b
            svp      = withTestDRG testDRG $ Prod.prooveSingleValue ck (Prod.SingleValueWitness a r)
            verified = Prod.verifySingleValue ck svp stmt
         in verifyNoFailReason (verifyResultD verified)

    {-
    testZero :: forall m n o . (Prod.ZeroConstraint m n o)
             => Proxy m -> Proxy n -> CommitmentKey n -> ECC.Scalar
             -> Matrix m n ECC.Scalar
             -> ListN m TEG.Random -> ListN m TEG.Random -> TestDRG -> Bool
    testZero pm _ ck bimapY a r s testDRG =
        let b = Matrix.fromList (ListN.replicate $ ECC.keyFromNum 1)
            a' = Matrix.fromRows $ updateA $ Matrix.toRows a
            witness  = Prod.ZeroWitness { Prod.zw_A = a'
                                        , Prod.zw_r = r
                                        , Prod.zw_B = b
                                        , Prod.zw_s = s }
            stmt     = Prod.zeroStmtFromWitness ck bimapY witness
            proof    = withTestDRG testDRG $ Prod.zeroProve bimapY ck witness
            verified = Prod.verifyZero ck proof stmt
         in verifyNoFailReason (verifyResultD verified)
      where
        m = natVal pm
        mm1 = natVal (Proxy @(m - 1))

        -- TODO: we need to make the last row to a to be the numerical inverse
        -- of the sum of all bimap of other column for the property of = 0
        -- to hold.
        updateA x = ListN.updateAt (Offset $ fromIntegral mm1) updateSum x
        updateSum x = x

        yInv = ECC.keyNegate bimapY
        -}

verifyNoFailReason :: Show a => [a] -> Bool
verifyNoFailReason [] = True
verifyNoFailReason l  = error (show l)
