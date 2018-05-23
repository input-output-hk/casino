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
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module Crypto.Casino.ZKSH.Product
    where

import           GHC.Generics
import           Basement.Nat
import           Basement.Types.OffsetSize
import           Data.Proxy
import           Data.Word (Word8)
import           Data.List (foldl1')
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
import           Control.DeepSeq
import           Control.Monad
import           Crypto.Random
import           Crypto.Casino.Primitives.ECC
import           Crypto.Casino.Primitives.SSize
import           Crypto.Casino.Primitives.Matrix (Matrix, DimensionsValid)
import qualified Crypto.Casino.Primitives.Matrix as Matrix
import           Crypto.Casino.Primitives.Commitment
import           Crypto.Casino.Primitives.HelperListN
import           Crypto.Casino.Primitives.TEG (Random)
import           Prelude hiding (product)

-- import qualified Crypto.Casino.Matrix as Matrix
import           Crypto.Casino.ZKSH.Types
import           Crypto.Casino.ZKSH.Operations

-- import           Debug.Trace

data Proof (m :: Nat) (n :: Nat) = Proof
    {
    -- initial message
      pp_Cb :: Commitment n
    -- SHVZK 5.1 argument of knowledge
    , pp_hadamardProduct :: HadamardProduct m n
    -- SHVZK 5.3 single value product argument of knowledge
    , pp_singleValue :: SingleValueProduct n
    } deriving (Show,Eq,Generic)

instance SSize (Proof m n) where
    type SizePoints (Proof m n) =
        SizePoints (Commitment n) +
        SizePoints (HadamardProduct m n) +
        SizePoints (SingleValueProduct n)
    type SizeScalar (Proof m n) =
        SizeScalar (Commitment n) +
        SizeScalar (HadamardProduct m n) +
        SizeScalar (SingleValueProduct n)

data Statement m n = Statement
    { stmt_ca :: ListN m (Commitment n)
    , stmt_b  :: Scalar
    } deriving (Show,Eq,Generic)

instance NFData (Proof m n)

data Witness m n = Witness
    { witness_a :: Matrix m n Z
    , witness_r :: ListN m Random
    } deriving (Show,Eq,Generic)

stmtFromWitness :: forall m n . ( DimensionsValid m n )
                => CommitmentKey n -> Witness m n -> Statement m n
stmtFromWitness ck (Witness a r) = Statement
    { stmt_ca = ca
    , stmt_b  = productScalar $ ListN.unListN bvec
    }
  where
    ca = ListN.zipWith (commitment ck) (Matrix.toRows a) r
    bvec = Matrix.foldRows (ListN.zipWith (#*)) a

-- SHVZK 5.1 argument of knowledge
data HadamardProduct (m :: Nat) (n :: Nat) = HadamardProduct
    { pphp_CB   :: ListN m (Commitment n)
    -- after challenge 'x', 'y'
    , pphp_zero :: Zero m n
    } deriving (Show,Eq,Generic)

instance SSize (HadamardProduct m n) where
    type SizePoints (HadamardProduct m n) =
        SizePoints (ListN m (Commitment n)) + SizePoints (Zero m n)
    type SizeScalar (HadamardProduct m n) =
        SizeScalar (ListN m (Commitment n)) + SizeScalar (Zero m n)

instance NFData (HadamardProduct m n)

data HadamardProductStatement m n = HadamardProductStatement
    { hp_stmt_cA :: ListN m (Commitment n)
    , hp_stmt_cb :: Commitment n
    } deriving (Show,Eq,Generic)

instance NFData (HadamardProductStatement m n)

newtype HadamardProductStatement2 m n = HadamardProductStatement2 (HadamardProductStatement m n)
    deriving (Show,Eq,Generic)

instance Challenge (HadamardProductStatement m n) where
    challenge (HadamardProductStatement ca cb) =
        hashFinalizeScalar $ cHashUpdate cb
                           $ cHashUpdate ca
                           $ cHashUpdate (0 :: Word8)
                           $ cHashInit

instance Challenge (HadamardProductStatement2 m n) where
    challenge (HadamardProductStatement2 (HadamardProductStatement ca cb)) =
        hashFinalizeScalar $ cHashUpdate cb
                           $ cHashUpdate ca
                           $ cHashUpdate (1 :: Word8)
                           $ cHashInit

data HadamardWitness m n = HadamardWitness
    { hw_A :: Matrix m n Scalar
    , hw_r :: ListN m Random
    , hw_b :: ListN n Scalar
    , hw_s :: Random
    } deriving (Show,Eq,Generic)

hadamardStmtFromWitness :: forall m n . ( DimensionsValid m n )
                        => CommitmentKey n -> HadamardWitness m n -> HadamardProductStatement m n
hadamardStmtFromWitness ck (HadamardWitness a r b s) =
    HadamardProductStatement (commitmentMatrix ck a r) (commitment ck b s)

-- SHVZK 5.2 zero argument of knowledge
data Zero (m :: Nat) (n :: Nat) = Zero
    { ppz_Ca0 :: Commitment n
    , ppz_Cbm :: Commitment n
    , ppz_CD  :: ListN (m+m+1) (Commitment n)
    -- after challenge 'x'
    , ppz_a :: ListN n Scalar
    , ppz_b :: ListN n Scalar
    , ppz_r :: Random
    , ppz_s :: Random
    , ppz_t :: Scalar
    } deriving (Show,Eq,Generic)

instance SSize (Zero m n) where
    type SizePoints (Zero m n) =
        SizePoints (Commitment n) + SizePoints (Commitment n) +
        SizePoints (ListN (m+m+1) (Commitment n)) +
        SizePoints (ListN n Scalar) + SizePoints (ListN n Scalar) +
        SizePoints Scalar + SizePoints Scalar + SizePoints Scalar
    type SizeScalar (Zero m n) =
        SizeScalar (Commitment n) + SizeScalar (Commitment n) +
        SizeScalar (ListN (m+m+1) (Commitment n)) +
        SizeScalar (ListN n Scalar) + SizeScalar (ListN n Scalar) +
        SizeScalar Scalar + SizeScalar Scalar + SizeScalar Scalar

instance NFData (Zero m n)

data ZeroWitness m n = ZeroWitness
    { zw_A :: Matrix m n Scalar
    , zw_r :: ListN m Random
    , zw_B :: Matrix m n Scalar
    , zw_s :: ListN m Random
    } deriving (Show,Eq,Generic)

data ZeroStatement (m :: Nat) (n :: Nat) = ZeroStatement
    { ppz_stmt_ca :: ListN m (Commitment n)
    , ppz_stmt_cb :: ListN m (Commitment n)
    , ppz_stmt_bilinear_map_y :: Scalar --
    } deriving (Show,Eq,Generic)

zeroStmtFromWitness :: forall m n . ( DimensionsValid m n )
                    => CommitmentKey n
                    -> Scalar            -- ^ bimap Y parameter
                    -> ZeroWitness m n
                    -> ZeroStatement m n
zeroStmtFromWitness ck bimapY (ZeroWitness a r b s) =
    ZeroStatement (commitmentMatrix ck a r) (commitmentMatrix ck b s) bimapY

instance NFData (ZeroStatement m n)

instance Challenge (ZeroStatement m n) where
    challenge (ZeroStatement ca cb y) =
        hashFinalizeScalar $ cHashUpdate y
                           $ cHashUpdate cb
                           $ cHashUpdate ca
                           $ cHashInit

-- SHVZK 5.3 single value product argument of knowledge
data SingleValueProduct (n :: Nat) = SingleValueProduct
    { ppsv_Cd :: Commitment n
    , ppsv_Cδ :: Commitment n
    , ppsv_CΔ :: Commitment n
    -- after challenge 'x'
    , ppsv_atilde :: ListN n Scalar
    , ppsv_btilde :: ListN n Scalar
    , ppsv_rtilde :: Scalar
    , ppsv_stilde :: Scalar
    } deriving (Show,Eq,Generic)

instance SSize (SingleValueProduct n) where
    type SizePoints (SingleValueProduct n) =
        SizePoints (Commitment n) + SizePoints (Commitment n) +
        SizePoints (Commitment n) + SizePoints (ListN n Scalar) +
        SizePoints (ListN n Scalar) + SizePoints Scalar + SizePoints Scalar
    type SizeScalar (SingleValueProduct n) =
        SizeScalar (Commitment n) + SizeScalar (Commitment n) +
        SizeScalar (Commitment n) + SizeScalar (ListN n Scalar) +
        SizeScalar (ListN n Scalar) + SizeScalar Scalar + SizeScalar Scalar

instance NFData (SingleValueProduct n)

data SingleValueProductStatement (n :: Nat) = SingleValueProductStatement
    { ppsv_stmt_ca :: Commitment n
    , ppsv_stmt_b  :: Scalar
    } deriving (Show,Eq,Generic)

instance NFData (SingleValueProductStatement n)

instance Challenge (SingleValueProductStatement n) where
    challenge (SingleValueProductStatement ca b) =
        hashFinalizeScalar $ cHashUpdate b
                           $ cHashUpdate ca
                           $ cHashInit

data SingleValueWitness n = SingleValueWitness
    { singleValueWitness_a :: ListN n Scalar
    , singleValueWitness_r :: Random
    } deriving (Show,Eq,Generic)

singleValueStmtFromWitness :: CommitmentKey n -> SingleValueWitness n -> SingleValueProductStatement n
singleValueStmtFromWitness ck (SingleValueWitness a r) =
    SingleValueProductStatement
        (commitment ck a r)
        (productScalar $ ListN.unListN a)

proove :: forall n m o k randomly
              . ( MonadRandom randomly
                , ProofDimensions m n o
                , KnownIntNat k
                , KnownIntNat (k+1)
                , (n * m) ~ o
                , k ~ (m + m))
              => CommitmentKey n
              -> Witness m n
              -> randomly (Proof m n)
proove ck (Witness a r) = do
    s <- keyGenerate

    let productA = Matrix.foldRows (ListN.zipWith (#*)) a
        cb = commitment ck productA s

    hd <- prooveHadamard ck (HadamardWitness a r productA s)
    sv <- prooveSingleValue ck (SingleValueWitness productA s)

    pure $ Proof cb hd sv

verify :: forall m n o .  ( ProofDimensions m n o )
       => CommitmentKey n
       -> Proof m n
       -> Statement m n
       -> Verify Bool
verify ck proof stmt =
    VerifyAnds "product"
        [ verifyHadamard ck (pp_hadamardProduct proof) (HadamardProductStatement (stmt_ca stmt) (pp_Cb proof))
        , verifySingleValue ck (pp_singleValue proof) (SingleValueProductStatement (pp_Cb proof) (stmt_b stmt))
        ]

prooveHadamard
    :: forall m n o mm1 randomly
     . ( DimensionsValid m n
       , ProofDimensions m n o
       , KnownIntNat mm1
       , (n * m) ~ o
       , (m - 1) ~ mm1
       , MonadRandom randomly
       )
    => CommitmentKey n
    -> HadamardWitness m n
    -> randomly (HadamardProduct m n)
prooveHadamard ck witness@(HadamardWitness a r b s) = do
    let avec = Matrix.toRows a
        bvec = ListN.toListN_ @m $ map (\i -> hadamardProduct $ take i (ListN.unListN avec)) [1..(fromIntegral m)]

    unless (ListN.index bvec (Offset $ fromIntegral m-1) == hadamardProduct (ListN.unListN avec)) $ error "invalid bvec"
    unless (b == hadamardProduct (ListN.unListN avec)) $ error "Product(a) /= b"

    svec <-   ListN.updateAt (Offset 0)                    (const $ ListN.index r 0)
            . ListN.updateAt (Offset $ fromIntegral m - 1) (const s)
            <$> randoms @m

    let cb = ListN.zipWith (commitment ck) bvec svec

    unless (ListN.index cb 0 == ListN.index (hp_stmt_cA stmt) 0) $
        error "Ca1 /= Cb1"

    -- compute d, its sum, and create the resulting dAndSum to pass as witness to the zero proof
    let d :: ListN mm1 (ListN n Scalar)
        d = ListN.zipWith (*|) (exponentsOfX @mm1 x) (ListN.init bvec)
        dsum = ListN.foldl1' (|+|) (ListN.zipWith (*|) (exponentsOfX x) (ListN.tail bvec))
        dAndSum :: ListN m (ListN n Scalar)
        dAndSum = rewriteListN_M1P1 (d `ListN.snoc` dsum)

        tvec = ListN.zipWith (#*) (exponentsOfX @mm1 x) (ListN.init svec)
        tsum = sumScalarN $ ListN.zipWith (#*) (exponentsOfX x) (ListN.tail svec)
        tvecAndSum = rewriteListN_M1P1 (tvec `ListN.snoc` tsum)

    let m1 = ListN.replicate $ keyNegate $ keyFromNum 1

    zeroArg <- zeroProve y ck
                         (ZeroWitness (Matrix.fromRows $ pushPop avec m1)
                                      (pushPop r (keyFromNum 0))
                                      (Matrix.fromRows dAndSum)
                                      tvecAndSum
                         )

    pure (HadamardProduct cb zeroArg)

  where
    m = natVal (Proxy @m)

    stmt = hadamardStmtFromWitness ck witness
    x = challenge stmt
    y = challenge (HadamardProductStatement2 stmt)

-- entry wise multiplication
hadamardProduct :: [ListN n Scalar] -> ListN n Scalar
hadamardProduct = foldl1' (ListN.zipWith (#*))

type ZeroConstraint m n o =
    ( ProofDimensions m n o
    , DimensionsValid (m+1) n
    , KnownIntNat (m+m+1)
    , KnownIntNat (m+1)
    )

-- | check if a zero witness is valid
--
-- the sum of the bilinear map between a and b should give the zero value
validZeroWitness :: ZeroConstraint m n o
                 => Scalar
                 -> ZeroWitness m n
                 -> Bool
validZeroWitness y (ZeroWitness a _ b _) =
    r == keyFromNum 0 -- || error (show a ++ "\n " ++ show b ++ "\n " ++ show r)
  where
    r     = sumScalarN $ ListN.zipWith bimap (Matrix.toRows a) (Matrix.toRows b)
    bimap = bimapWith y

zeroProve :: forall m n o k ksucc randomly .
             ( ZeroConstraint m n o
             , MonadRandom randomly
             , (m + m) ~ k
             , (k + 1) ~ ksucc)
          => Scalar                    -- ^ bimap y parameter
          -> CommitmentKey n           -- ^ ck
          -> ZeroWitness m n
          -> randomly (Zero m n)
zeroProve bimapY ck witness@(ZeroWitness a rvec b svec) = do
    a0 <- randoms @n
    bm <- randoms @n
    r0 <- keyGenerate
    sm <- keyGenerate

    unless (validZeroWitness bimapY witness) $ error "zero prove: invalid witness"

    let ca0 = commitment ck a0 r0
        cBm = commitment ck bm sm

    let bimap = bimapWith bimapY

    let d :: ListN (k+1) Scalar
        d =
            let  -- sum of ai `bimap` bj
                a' = Matrix.toRows (a0 `Matrix.prependRow` a)
                b' = Matrix.toRows (b `Matrix.appendRow` bm)
                calculate k = sumScalar $ map (\(i, j) -> bimap (ListN.index a' i) (ListN.index b' j)) iters
                  where iters = [ (Offset i,Offset j)
                                | i <- [0..fromIntegral m], j <- [0..fromIntegral m], j == fromIntegral (m-fromIntegral k)+i
                                ]
             in ListN.create $ \k -> calculate k

    tvec <- ListN.updateAt (Offset $ fromIntegral m + 1) (const $ keyFromNum 0)
            <$> randoms @(k+1)

    let cd = ListN.zipWith (\di ti -> commitment ck (extend0 di) ti) d tvec

    let expX    = exponentsOfXFrom1 x
        revExpX = ListN.reverse expX

    let avec = ListN.foldl1' (|+|)
             $ ListN.zipWith (*|) expX
                                  (Matrix.toRows $ Matrix.prependRow a0 a)
        bvec = ListN.foldl1' (|+|)
             $ ListN.zipWith (*|) revExpX (Matrix.toRows $ Matrix.appendRow b bm)

        r = sumScalarN $ ListN.zipWith (#*) expX (r0 `ListN.cons` rvec)
        s = sumScalarN $ ListN.zipWith (#*) revExpX (svec `ListN.snoc` sm)
        t = sumScalarN $ ListN.zipWith (#*) (exponentsOfXFrom1 x) tvec

    pure $ Zero { ppz_Ca0 = ca0
                , ppz_Cbm = cBm
                , ppz_CD  = cd
                , ppz_a   = avec
                , ppz_b   = bvec
                , ppz_r   = r
                , ppz_s   = s
                , ppz_t   = t
                }
  where
    m = natVal (Proxy @m)

    stmt = zeroStmtFromWitness ck bimapY witness
    x = challenge stmt

    extend0 v = ListN.create $ \i -> if i == 0 then v else keyFromNum 0

bimapWith :: (1 <= n, NatWithinBound Int n, KnownNat n)
          => Scalar
          -> ListN n Scalar
          -> ListN n Scalar
          -> Scalar
bimapWith y a d = sumScalarN $
    ListN.zipWith (#*) (exponentsOfX y) (ListN.zipWith (#*) a d)

type SingleValueConstraint n = (NatWithinBound Int n, KnownNat n, 1 <= n)

prooveSingleValue
    :: forall n randomly
     . ( MonadRandom randomly, SingleValueConstraint n)
    => CommitmentKey n
    -> SingleValueWitness n
    -> randomly (SingleValueProduct n)
prooveSingleValue ck witness@(SingleValueWitness a r) = do
    let b = ListN.toListN_ $ map (\i -> productScalar $ take i (ListN.unListN a)) [1..(fromIntegral n)]
    d  <- randoms @n
    rd <- keyGenerate
    delta <- ListN.updateAt (Offset 0)                    (const $ ListN.index d 0) .
             ListN.updateAt (Offset $ fromIntegral n - 1) (const $ keyFromNum 0)
             <$> randoms @n
    s1 <- keyGenerate
    sx <- keyGenerate

    let cd = commitment ck d rd
        cdelta = commitment ck (makeList_delta d delta) s1
        cDelta = commitment ck (makeList_Delta delta b d) sx

    let x = challenge $ singleValueStmtFromWitness ck witness

    let aTilde = ListN.zipWith (\ai di -> (x #* ai) #+ di) a d
        bTilde = ListN.zipWith (\bi di -> (x #* bi) #+ di) b delta
        rTilde = (x #* r) #+ rd
        sTilde = (x #* sx) #+ s1

    pure $ SingleValueProduct cd cdelta cDelta
                              aTilde bTilde rTilde sTilde
  where
    n = natVal (Proxy @n)

    -- create the list of commited values for delta. This list is n-1 long,
    -- and expended to n for commitment
    makeList_delta d delta = rewriteListN_M1P1 (comList `ListN.snoc` keyFromNum 0)
      where
        comList = ListN.zipWith (\x y -> keyNegate (x #* y)) (ListN.init delta) (ListN.tail d)

    makeList_Delta delta b d = rewriteListN_M1P1 (comList `ListN.snoc` keyFromNum 0)
      where
        comList = ListN.zipWith5
                (\deltaNext aNext deltaCur bCur dNext ->
                    deltaNext #- (aNext #* deltaCur) #- (bCur #* dNext))
                (ListN.tail delta)
                (ListN.tail a)
                (ListN.init delta)
                (ListN.init b)
                (ListN.tail d)

verifyHadamard :: forall m n o .
    ( ProofDimensions m n o )
    => CommitmentKey n
    -> HadamardProduct m n
    -> HadamardProductStatement m n
    -> Verify Bool
verifyHadamard ck proof stmt =
    VerifyAnds "hadamard product"
        [ (:==:) "cb1 = ca1"
                (ListN.index (hp_stmt_cA stmt) 0)
                (ListN.index (pphp_CB proof) 0)
        , (:==:) "cbm = cb"
                (hp_stmt_cb stmt)
                (ListN.index (pphp_CB proof) (Offset $ m-1))
        , verifyZero ck (pphp_zero proof) $ ZeroStatement { ppz_stmt_ca = zeroCa
                                                          , ppz_stmt_cb = zeroCb
                                                          , ppz_stmt_bilinear_map_y = y }
        ]
  where
    m = natValInt (Proxy @m)
    x = challenge stmt
    y = challenge (HadamardProductStatement2 stmt)

    zeroCa = pushPop (hp_stmt_cA stmt) cm1
      where cm1 = commitment ck m1 (keyFromNum 0)
            m1 = ListN.replicate $ keyNegate $ keyFromNum 1
    zeroCb = rewriteListN_M1P1 (cdi `ListN.snoc` cdsum)
      where cdi = ListN.zipWith commitmentExponentiate (ListN.init $ pphp_CB proof) (exponentsOfX x)
            cdsum = commitmentProd $ ListN.zipWith commitmentExponentiate (ListN.tail $ pphp_CB proof) (exponentsOfX x)


verifyZero :: forall m n o msucc k ksucc .
             ( ProofDimensions m n o
             , DimensionsValid (m+1) n
             , (m + m) ~ k
             , (m + 1) ~ msucc
             , (k + 1) ~ ksucc
             , KnownIntNat (k+1)
             , KnownIntNat (m+1))
           => CommitmentKey n
           -> Zero m n
           -> ZeroStatement m n
           -> Verify Bool
verifyZero ck proof stmt =
    VerifyAnds "zero value"
        [ (:==:) "Cdm1 == com(0,0)"
            (ListN.index (ppz_CD proof) (Offset m+1))
            (commitment ck (ListN.replicate @n $ keyFromNum 0) (keyFromNum 0))
        , (:==:) "C_ai^x^i = com_ck(a, r)"
            (commitmentProd @msucc $ ListN.zipWith commitmentExponentiate
                (ppz_Ca0 proof `ListN.cons` ppz_stmt_ca stmt) (exponentsOfXFrom1 x))
            (commitment ck (ppz_a proof) (ppz_r proof))
        , (:==:) "(C_bj^x^(m-j)) = com_ck(b, s)"
            (commitmentProd @msucc $ ListN.zipWith commitmentExponentiate
                (ppz_stmt_cb stmt `ListN.snoc` ppz_Cbm proof) (ListN.reverse $ exponentsOfXFrom1 x))
            (commitment ck (ppz_b proof) (ppz_s proof))
        , (:==:) "(C_Dk^x^k) = com_ck(a bimap b, t)"
            (commitmentProd $ ListN.zipWith commitmentExponentiate
                (ppz_CD proof)
                (exponentsOfXFrom1 x))
            (commitment ck (extendSingletonWithZero (ppz_a proof `bimap` ppz_b proof)) (ppz_t proof))
        ]
  where
    bimap = bimapWith (ppz_stmt_bilinear_map_y stmt)
    x = challenge stmt
    m = natValInt (Proxy @m)

verifySingleValue
    :: forall n . (SingleValueConstraint n)
    => CommitmentKey n
    -> SingleValueProduct n
    -> SingleValueProductStatement n
    -> Verify Bool
verifySingleValue ck svp stmt@(SingleValueProductStatement ca b) =
    VerifyAnds "single value product"
        [ (:==:) "com(atilde)==ca^x*cd"
                 com1 (commitmentCombineExp ca (ppsv_Cd svp))
        , (:==:) "com(xbi-biai)==cDelta^x*cdelta"
                 com2 (commitmentCombineExp (ppsv_CΔ svp) (ppsv_Cδ svp))
        , (:==:) "b1~ = a1~"
                 (ListN.index (ppsv_atilde svp) 0)
                 (ListN.index (ppsv_btilde svp) 0)
        , (:==:) "bn~ = x * b"
                 (x #* b)
                 (ListN.index (ppsv_btilde svp) (Offset $ fromIntegral n-1))
        ]
  where
    n = natVal (Proxy @n)
    com1 = commitment ck (ppsv_atilde svp) (ppsv_rtilde svp)

    x = challenge stmt
    com2 = commitment ck bMinusBA (ppsv_stilde svp)

    -- make the `x * b_i+1 - b_i * a_i+1` list
    bMinusBA = rewriteListN_M1P1 (comList `ListN.snoc` keyFromNum 0)
      where
        comList = ListN.zipWith3
            (\bNext bCur aNext -> (x #* bNext) #- (bCur #* aNext))
            (ListN.tail $ ppsv_btilde svp)
            (ListN.init $ ppsv_btilde svp)
            (ListN.tail $ ppsv_atilde svp)

    commitmentCombineExp c1 c2 = (c1 `commitmentExponentiate` x) `commitmentMul` c2
