{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import           Gauge.Main
import           Data.Proxy
import           Data.Word
import           Control.Monad
import           Control.DeepSeq
import           Basement.Bounded
import           Basement.Nat
import qualified Basement.UArray as A
import           Basement.From
import qualified Basement.Sized.List as ListN
import qualified Crypto.Casino.Primitives.Permutation as Permutation
import qualified Crypto.Casino.Primitives.TEG as TEG
import qualified Crypto.Casino.Primitives.Commitment as Commitment

import           Crypto.Casino.Primitives.SSize
import qualified Crypto.Casino.Primitives.ECC as ECC
import qualified Crypto.Poker.Card as Card
import qualified Crypto.Casino.ZKSH as ZKSH

import qualified Crypto.PubKey.Ed25519 as Ed25519

data SomeNatInt = forall n. (KnownNat n, NatWithinBound Int n) => SomeNatInt (Proxy n)

data CommitmentSetup = forall n . (NatWithinBound Int n, KnownNat n)
    => CommitmentSetup !(Commitment.CommitmentKey n)

commitmentSetup :: [SomeNatInt] -> IO [CommitmentSetup]
commitmentSetup prxs = mapM (\(SomeNatInt prx) -> mk prx) prxs
  where
    mk :: forall n . (NatWithinBound Int n, KnownNat n) => Proxy n -> IO CommitmentSetup
    mk _ = CommitmentSetup <$> Commitment.keyNew @n

commitmentBenchs :: CommitmentSetup -> Benchmark
commitmentBenchs (CommitmentSetup wrappedKey) = withKey wrappedKey
  where
    withKey :: forall n . (NatWithinBound Int n, KnownNat n)
            => Commitment.CommitmentKey n
            -> Benchmark
    withKey key =
        bench ("n=" ++ show n) $ nf (\l -> Commitment.commitment key l r) list
      where
        n = natVal (Proxy @n)
        !r = ECC.keyFromNum 10
        list :: ListN.ListN n ECC.Scalar
        list = ListN.create (\i -> ECC.keyFromNum (fromIntegral i + 2))

tegSetup :: IO [(TEG.PublicBroadcast, TEG.SecretKey)]
tegSetup = replicateM 100 TEG.generation

tegBenchs name keys = do
    let jointKey = TEG.combine $ map fst keys
    !cipherText <- TEG.encryption jointKey (TEG.integerToMessage 50)
    !dshares    <- mapM (\((pk,_), sk) -> (pk,) <$> TEG.decryptShare sk cipherText) keys
    pure $ bgroup name
        [ bench "verify shares" $ nf (map TEG.publicBroadcastVerify) (map fst keys)
        , bench "create-joint-pk" $ nf TEG.combine $ map fst keys
        , bench "decrypt all shares" $ nfIO $ mapM (\((pk,_), sk) -> (pk,) <$> TEG.decryptShare sk cipherText) keys
        , bench "open public" $ nf (\shares -> TEG.integerFromMessage <$> TEG.verifiableDecrypt shares cipherText) dshares
        , bench "open private" $ nf (\shares ->
                    case shares of
                        [] -> error "no shares"
                        (_,(dsp,_)):otherShares ->
                            TEG.integerFromMessage <$> TEG.verifiableDecryptOwn dsp otherShares cipherText) dshares
        ]

-- shuffle is parametrized by n and m, the number of ciphertext,

data AnyShuffleProof = forall (m :: Nat) (n :: Nat) . AnyShuffleProof !(ZKSH.ShuffleProof m n)

instance NFData AnyShuffleProof where
    rnf (AnyShuffleProof p) = rnf p

randomizeBenchs
    :: GameSetup
    -> IO Benchmark
randomizeBenchs (GameSetup a b c d e f g) = do
    mkShuffle a b c d e f g
  where
    showNatVal :: KnownNat x => Proxy x -> String
    showNatVal = show . natVal
    mkShuffle :: forall m n o p
         . (ZKSH.ProofDimensions m n o, NatWithinBound Int p)
        => ListN.ListN p TEG.SecretKey
        -> TEG.JointPublicKey
        -> ListN.ListN o TEG.Ciphertext
        -> Proxy m
        -> Proxy n
        -> Proxy o
        -> Commitment.CommitmentKey n
        -> IO Benchmark
    mkShuffle players jpk cards m n o ck = do
        let paramNames = "cards=" ++ showNatVal o
        perm <- Permutation.randomize Permutation.identity

        pure $ bench paramNames $ nfIO $ do
            r    <- ListN.replicateM TEG.randomNew

            let permutedCards = Permutation.apply perm cards
                cards' = ListN.zipWith (TEG.reRandomize jpk) r permutedCards
            pure cards'

shuffleBenchs
    :: GameSetup
    -> IO Benchmark
shuffleBenchs (GameSetup a b c d e f g) = do
    mkShuffle a b c d e f g
  where
    showNatVal :: KnownNat x => Proxy x -> String
    showNatVal = show . natVal
    mkShuffle :: forall m n o p
         . (ZKSH.ProofDimensions m n o, NatWithinBound Int p)
        => ListN.ListN p TEG.SecretKey
        -> TEG.JointPublicKey
        -> ListN.ListN o TEG.Ciphertext
        -> Proxy m
        -> Proxy n
        -> Proxy o
        -> Commitment.CommitmentKey n
        -- -> IO AnyShuffleProof
        -> IO Benchmark
    mkShuffle players jpk cards m n o ck = do
        let paramNames = "cards=" ++ showNatVal o ++ " m=" ++ showNatVal m ++ " n=" ++ showNatVal n
            unshuffled = ZKSH.UnShuffled cards
        perm <- Permutation.randomize Permutation.identity
        r    <- ListN.replicateM TEG.randomNew
        let witness = ZKSH.Witness perm r
            stmt = ZKSH.stmtFromWitness jpk witness unshuffled

        --let !permutedCards = Permutation.apply perm cards
        --    !cards' = ListN.zipWith (TEG.reRandomize jpk) r permutedCards

        pure $ witness
            `deepseq` bench paramNames $ nfIO (AnyShuffleProof <$> ZKSH.shuffleProve @m jpk ck witness unshuffled)

validationBenchs
    :: GameSetup
    -> IO Benchmark
validationBenchs (GameSetup a b c d e f g) = do
    mkShuffle a b c d e f g
  where
    showNatVal :: KnownNat x => Proxy x -> String
    showNatVal = show . natVal
    mkShuffle :: forall m n o p
         . (ZKSH.ProofDimensions m n o, NatWithinBound Int p)
        => ListN.ListN p TEG.SecretKey
        -> TEG.JointPublicKey
        -> ListN.ListN o TEG.Ciphertext
        -> Proxy m
        -> Proxy n
        -> Proxy o
        -> Commitment.CommitmentKey n
        -- -> IO AnyShuffleProof
        -> IO Benchmark
    mkShuffle players jpk cards m n o ck = do
        let paramNames = "cards=" ++ showNatVal o ++ " m=" ++ showNatVal m ++ " n=" ++ showNatVal n
            unshuffled = ZKSH.UnShuffled cards
        perm <- Permutation.randomize Permutation.identity
        r    <- ListN.replicateM TEG.randomNew
        let witness = ZKSH.Witness perm r
            stmt = ZKSH.stmtFromWitness jpk witness unshuffled

        -- let !permutedCards = Permutation.apply perm cards
        --    !cards' = ListN.zipWith (TEG.reRandomize jpk) r permutedCards

        !proof <- ZKSH.shuffleProve @m jpk ck witness unshuffled

        pure $ proof
            `deepseq` bench paramNames $ nf (\stmt -> ZKSH.verifyResult $ ZKSH.shuffleVerify @m jpk ck proof stmt) stmt

data GameSetup =
      forall m n o p
    . (ZKSH.ProofDimensions m n o, NatWithinBound Int p) => GameSetup
        { gamePlayers  :: ListN.ListN p TEG.SecretKey
        , gameJointKey :: TEG.JointPublicKey
        , gameCards    :: ListN.ListN o TEG.Ciphertext
        , gameM        :: Proxy m
        , gameN        :: Proxy n
        , gameO        :: Proxy o
        , gameCommitKey :: Commitment.CommitmentKey n
        }

setupGame
    :: forall m n o p
     . (ZKSH.ProofDimensions m n o, KnownNat p, NatWithinBound Int p) -- , o ~ 52)
    => Proxy m
    -> Proxy n
    -> Proxy o
    -> Proxy p
    -> IO GameSetup
setupGame m n o _ = do
    players <- ListN.replicateM @p TEG.generation
    -- let cards = Card.newDeck
    --    idxes = ListN.map Card.cardToIndex cards
    let idxes = ListN.create id
    let     jpk   = TEG.combine $ ListN.unListN $ ListN.map fst players

    ck <- Commitment.keyNew

    ciphers <- ListN.mapM (TEG.encryption jpk . TEG.integerToMessage . from) idxes

    pure $ GameSetup
        { gamePlayers  = ListN.map snd players
        , gameJointKey = jpk
        , gameCards    = ciphers
        , gameM        = m
        , gameN        = n
        , gameO        = o
        , gameCommitKey = ck
        }

showProofSize :: forall m n
    . (KnownNat m, KnownNat n
      , KnownNat (SizePoints (ZKSH.ShuffleProof m n))
      , KnownNat (SizeScalar (ZKSH.ShuffleProof m n)))
    => Proxy m -> Proxy n -> String
showProofSize _ _ =
    "m=" ++ show (natVal (Proxy @m)) ++
    " n=" ++ show (natVal (Proxy @n)) ++
    " => points=" ++ show (natVal (Proxy @(SizePoints (ZKSH.ShuffleProof m n)))) ++
    " ,  scalars=" ++ show (natVal (Proxy @(SizeScalar (ZKSH.ShuffleProof m n))))

main :: IO ()
main = do
    putStrLn "### shuffle proof size ###"
    putStrLn (showProofSize @5 @5 Proxy Proxy)
    putStrLn (showProofSize @5 @10 Proxy Proxy)
    putStrLn (showProofSize @5 @100 Proxy Proxy)
    putStrLn (showProofSize @4 @13 Proxy Proxy)
    putStrLn (showProofSize @4 @26 Proxy Proxy)
    putStrLn (showProofSize @8 @26 Proxy Proxy)

    tegEnv <- replicateM 100 TEG.generation

    comEnv <- commitmentSetup [ SomeNatInt @2 Proxy
                              , SomeNatInt @4 Proxy
                              , SomeNatInt @6 Proxy
                              , SomeNatInt @8 Proxy
                              , SomeNatInt @10 Proxy
                              , SomeNatInt @12 Proxy
                              ]

    tegs <- mapM (\i -> tegBenchs ("players=" ++ show i) $ take i tegEnv) [2, 4, 6, 8, 10, 12]
    let coms = map commitmentBenchs comEnv

    game52    <- setupGame (Proxy @4) (Proxy @13) (Proxy @52) (Proxy @4)
    game52_2  <- setupGame (Proxy @2) (Proxy @26) (Proxy @52) (Proxy @4)
    game104   <- setupGame (Proxy @8) (Proxy @13) (Proxy @104) (Proxy @4)
    game104_2 <- setupGame (Proxy @4) (Proxy @26) (Proxy @104) (Proxy @4)
    game208   <- setupGame (Proxy @16) (Proxy @13) (Proxy @208) (Proxy @4)
    game208_2 <- setupGame (Proxy @8) (Proxy @26) (Proxy @208) (Proxy @4)

    permutationBenchs <- mapM randomizeBenchs [game52, game104, game208]
    permProofBenchs <- mapM shuffleBenchs [game52, game52_2, game104, game104_2, game208, game208_2 ]
    permValidationBenchs <- mapM validationBenchs [game52, game52_2, game104, game104_2, game208, game208_2 ]

    !sk <- Ed25519.generateSecretKey
    let !msg100 = A.replicate 100 0 :: A.UArray Word8
        !pk = Ed25519.toPublic sk
        !sig = Ed25519.sign sk pk msg100

    defaultMain $
        [
        -- --- primitives ---
          bgroup "commitment" coms
        , bgroup "ed25519"
            [ bench "signature" $ nf (Ed25519.sign sk pk) msg100
            , bench "verify" $ nf (\ba -> Ed25519.verify pk ba sig) msg100
            ]
        , bgroup "shuffle"
            [ bgroup "randomization" permutationBenchs
            , bgroup "permutation" permProofBenchs
            , bgroup "verification" permValidationBenchs
            ]
        , bgroup "ciphertext"
            ([ bench "generate-key (each player locally)" $ nfIO TEG.generation
             ] ++ tegs
            )
        -- --- game primitives ---
        , bgroup "opening" []
        ]
