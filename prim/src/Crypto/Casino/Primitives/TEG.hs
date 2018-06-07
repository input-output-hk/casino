--
-- implementation of:
--   2.2 (n-n)-Threshold ElGamal Cryptosystem
--
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
module Crypto.Casino.Primitives.TEG
    ( SecretKey
    , PublicKey
    , PublicBroadcast
    , DecryptBroadcast
    , DecryptSharePoint
    , Ciphertext
    , JointPublicKey
    , Random
    , Message
    , debugHash
    , generation
    , randomNew
    , combine
    , combineVerify
    , reEncrypter
    , publicBroadcastVerify
    , ciphertextCreate
    , ciphertextAdd
    , ciphertextMul
    , ciphertextSum
    , ciphertextProduct
    , ciphertextScale
    , ciphertextToPoints
    , productCiphertextExponentiate
    , encryption
    , encryptionWith
    , encryptionRandom1
    , reRandomize
    , decryptShare
    , decryptShareNoProof
    , verifiableDecrypt
    , verifiableDecryptOwn
    , integerToMessage
    , integerFromMessage
    , bilinearMap
    , properties
    ) where

import           Control.DeepSeq
import           Crypto.Random
import           Crypto.Casino.Primitives.ECC hiding (PrivateKey, PublicKey)
import           Crypto.Casino.Primitives.SSize
import           Crypto.Hash (Blake2b, Digest, hash)
import qualified Crypto.Casino.Primitives.DLOG as DLOG
import qualified Crypto.Casino.Primitives.DLEQ as DLEQ
import           Data.List (foldl')
import           GHC.Generics
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN

import           Foundation.Check
import qualified Data.ByteString as B

type PublicKey = Point
type SecretKey = Scalar
type Random = Scalar

newtype DecryptSharePoint = DecryptSharePoint Point
    deriving (Show,Eq,Generic)

instance NFData DecryptSharePoint

type PublicBroadcast = (PublicKey, DLOG.Proof)
type DecryptBroadcast = (DecryptSharePoint, DLEQ.Proof)

data Ciphertext = Ciphertext Point Point
    deriving (Show,Eq,Generic)

-- | This is stricly used for printing for debug
debugHash :: Ciphertext -> String
debugHash (Ciphertext p1 p2) =
    show (hash (pointToBinary p1 `B.append` pointToBinary p2) :: Digest (Blake2b 32))

ciphertextToPoints :: Ciphertext -> (Point, Point)
ciphertextToPoints (Ciphertext a b) = (a,b)

instance SSize Ciphertext where
    type SizePoints Ciphertext = 2
    type SizeScalar Ciphertext = 0

instance NFData Ciphertext

type Message = Point

newtype JointPublicKey = JointPublicKey Point
    deriving (Show,Eq,Generic,Arbitrary)

instance NFData JointPublicKey

data HomomorphicTest = HomomorphicTest Point Point Point Point
    deriving (Show,Eq)

instance Arbitrary HomomorphicTest where
    arbitrary = HomomorphicTest <$> arbitrary <*> arbitrary
                                <*> arbitrary <*> arbitrary

instance Arbitrary Ciphertext where
    arbitrary = Ciphertext <$> arbitrary <*> arbitrary

-- koblitz probabilistic encoding/decoding k parameter
k :: Integer
k = 7919

integerFromMessage :: Message -> Integer
integerFromMessage = koblitzDecode . pointToX
  where
    koblitzDecode x = (x - 1) `div` k

-- maximum integer number is ((p-1)/2) / k
integerToMessage :: Integer -> Message
integerToMessage n = koblitzEncode (n * k + 1)
  where
    upperLimit = (n+1) * k
    -- probability of failure to find a sqrt is extremely small considering k : 1 / (2^k)
    koblitzEncode i
        | i == upperLimit = error "integerToMessage: cannot find a valid message"
        | otherwise       =
            case pointFromX i of
                Just p  -> p
                Nothing -> koblitzEncode (i+1)

randomNew :: MonadRandom random => random Random
randomNew = keyGenerate

generation :: MonadRandom random => random (PublicBroadcast, SecretKey)
generation = addPublicBroadcast <$> keyGenerate
                                <*> keyGenerate
  where
    addPublicBroadcast :: SecretKey -> Random -> (PublicBroadcast, SecretKey)
    addPublicBroadcast sk dlogR = ((hi, dlog), sk)
          where
            dlog = DLOG.generate dlogR sk (DLOG.DLOG curveGenerator hi)
            hi = pointFromSecret sk

publicBroadcastVerify :: PublicBroadcast -> Bool
publicBroadcastVerify (pk, dlog) = DLOG.verify (DLOG.DLOG curveGenerator pk) dlog

combine :: [PublicBroadcast] -> JointPublicKey
combine l = JointPublicKey $ foldl' (.+) pointIdentity $ map fst l

combineVerify :: [PublicBroadcast] -> Maybe JointPublicKey
combineVerify l
    | and $ fmap publicBroadcastVerify l = Just $ combine l
    | otherwise                          = Nothing

encryption :: MonadRandom random => JointPublicKey -> Message -> random Ciphertext
encryption pk msg = encryptionWith pk msg <$> keyGenerate

encryptionWith :: JointPublicKey -> Message -> Random -> Ciphertext
encryptionWith (JointPublicKey pk) msg r = Ciphertext c1 c2
  where c1 = pointFromSecret r
        c2 = (pk .* r) .+ msg

-- | Encrypt with a deterministic random equal 1
encryptionRandom1 :: JointPublicKey -> Message -> Ciphertext
encryptionRandom1 jpk msg =
    encryptionWith jpk msg (keyFromNum 1)

reEncrypter :: JointPublicKey -> Random -> Ciphertext
reEncrypter jpk = encryptionWith jpk pointIdentity

reRandomize :: JointPublicKey -> Random -> Ciphertext -> Ciphertext
reRandomize jpk r c = reEncrypter jpk r `ciphertextMul` c

decryptShare :: MonadRandom random
             => SecretKey
             -> Ciphertext
             -> random DecryptBroadcast
decryptShare sk (Ciphertext c1 _) = toDecryptBroadcast <$> keyGenerate
  where
    !d = c1 .* sk
    pk = pointFromSecret sk
    toDecryptBroadcast dleqR =
        (DecryptSharePoint d, DLEQ.generate dleqR sk (DLEQ.DLEQ curveGenerator pk c1 d))

decryptShareNoProof :: SecretKey
                    -> Ciphertext
                    -> DecryptSharePoint
decryptShareNoProof sk (Ciphertext c1 _) = DecryptSharePoint d where !d = c1 .* sk

verifiableDecrypt :: [(PublicKey, DecryptBroadcast)] -- ^ decrypt broadcast associated with their public key
                  -> Ciphertext
                  -> Maybe Message
verifiableDecrypt decrypts (Ciphertext c1 c2)
    | allVerify = Just (c2 .- sumds)
    | otherwise = Nothing
  where
    allVerify = and $ map (\(pk, (DecryptSharePoint di, dleq)) -> DLEQ.verify (DLEQ.DLEQ curveGenerator pk c1 di) dleq) decrypts
    sumds = foldl' (.+) pointIdentity $ map fst decrypts

verifiableDecryptOwn :: DecryptSharePoint
                     -> [(PublicKey, DecryptBroadcast)]
                     -> Ciphertext
                     -> Maybe Message
verifiableDecryptOwn (DecryptSharePoint selfP) decrypts ct =
    case verifiableDecrypt decrypts ct of
        Nothing -> Nothing
        Just m  -> Just (m .+ selfP)

ciphertextCreate :: Scalar -> Point -> Ciphertext
ciphertextCreate a b = Ciphertext (pointFromSecret a) b

ciphertextAdd :: Ciphertext -> Ciphertext -> Ciphertext
ciphertextAdd (Ciphertext c1a c1b) (Ciphertext c2a c2b) = Ciphertext (c1a .+ c2a) (c1b .+ c2b)
{-# DEPRECATED ciphertextAdd "use ciphertextMul" #-}

ciphertextMul :: Ciphertext -> Ciphertext -> Ciphertext
ciphertextMul (Ciphertext c1a c1b) (Ciphertext c2a c2b) = Ciphertext (c1a .+ c2a) (c1b .+ c2b)

ciphertextScale :: Scalar -> Ciphertext -> Ciphertext
ciphertextScale s (Ciphertext c1 c2) = Ciphertext (c1 .* s) (c2 .* s)

ciphertextIdentity :: Ciphertext
ciphertextIdentity = Ciphertext pointIdentity pointIdentity

ciphertextSum :: [Ciphertext] -> Ciphertext
ciphertextSum = foldl' ciphertextAdd ciphertextIdentity
{-# DEPRECATED ciphertextSum "use ciphertextProduct" #-}

ciphertextProduct :: [Ciphertext] -> Ciphertext
ciphertextProduct = foldl' ciphertextAdd ciphertextIdentity

productCiphertextExponentiate :: ListN n Ciphertext -> ListN n Scalar -> Ciphertext
productCiphertextExponentiate =
      ((ciphertextProduct . ListN.unListN) .)
    . ListN.zipWith (flip ciphertextScale)

bilinearMap :: ListN n Ciphertext -> ListN n Scalar -> Ciphertext
bilinearMap = productCiphertextExponentiate

properties :: Test
properties = Group "TEG"
    [ Group "math"
        [ Property "eq" $ \(x :: Ciphertext) -> x == x
        , Property "right-identity" $ \x -> (x `ciphertextAdd` ciphertextIdentity) == x
        , Property "left-identity" $ \x -> (ciphertextIdentity `ciphertextAdd` x) == x
        , Property "commutative" $ \x1 x2 -> (x1 `ciphertextAdd` x2) == (x2 `ciphertextAdd` x1)
        , Property "associative" $ \x1 x2 x3 ->
            (x1 `ciphertextAdd` x2) `ciphertextAdd` x3 == x1 `ciphertextAdd` (x2 `ciphertextAdd` x3)
        , Property "scale-x2" $ \x -> ciphertextScale (keyFromNum 2) x == (x `ciphertextAdd` x)
        , Property "scale-x3" $ \x -> ciphertextScale (keyFromNum 3) x == ((x `ciphertextAdd` x) `ciphertextAdd` x)
        ]
    , Group "homomorphic" $
        [ Property "plus" $ \m1 m2 p1 p2 ->
            Ciphertext (m1 .+ m2) (p1 .+ p2) == ciphertextAdd (Ciphertext m1 p1) (Ciphertext m2 p2)
        , Property "scale" $ \m1 p1 s ->
            Ciphertext (m1 .* s) (p1 .* s) == ciphertextScale s (Ciphertext m1 p1)
        , Property "scale-commutative" $ \m1 p1 s1 s2 ->
            let ct = Ciphertext m1 p1
             in (ciphertextScale s1 . ciphertextScale s2) ct == (ciphertextScale s2 . ciphertextScale s1) ct
        -- , Property "scale2" $ \m1 p1 s1 ->
        --     Ciphertext (m1 .* (s1 #+ keyFromNum 1)) (p1 .* (s1 #+ keyFromNum 1)) == (ciphertextScale s1 . ciphertextScale (keyFromNum 1)) (Ciphertext m1 p1)
        ]
    ]
