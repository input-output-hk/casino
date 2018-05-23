{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
module Crypto.Casino.Primitives.ECC
    ( Point(..)
    , Scalar(..)
    , PublicKey(..)
    , PrivateKey(..)
    , KeyPair(..)
    , DhSecret(..)
    , curveGenerator
    , pointToDhSecret
    , pointFromSecret
    , pointIdentity
    , pointToBinary
    , scalarToBinary
    , keyPairGenerate
    , keyGenerate
    , keyFromBytes
    , keyFromNum
    , keyInverse
    , keyNegate
    , (#+)
    , (#-)
    , (#*)
    , (#^)
    , (.+)
    , (.-)
    , (.*)
    , (*.)
    , mulAndSum
    , mulPowerAndSum
    , hashPoints
    , hashUpdatePoints
    , hashPointsToKey
    , hashFinalizeScalar
    , pointFromX
    , pointToX
    ) where

#define OPENSSL

import           Data.ByteString (ByteString)
import qualified Data.ByteString as B
import qualified Data.ByteArray as B (convert)
import           Data.Bits
import           Data.Binary
import           Data.Binary.Get (getByteString)
import           Data.Binary.Put (putByteString)
import           Data.List (foldl')

import           GHC.Generics
import           Control.DeepSeq
import           Crypto.Hash (hash, hashUpdate, hashFinalize, Context, SHA256, Digest)
import           Crypto.Number.Serialize
import           Crypto.Number.ModArithmetic (expFast)
import           Crypto.Casino.Primitives.SSize
import           Crypto.Random
import           Control.Exception
import           System.IO.Unsafe

#ifdef OPENSSL
import qualified Crypto.OpenSSL.ECC as SSL
import GHC.Integer.GMP.Internals (recipModInteger)
import Crypto.Number.Generate
import Crypto.PubKey.ECC.Types (getCurveByName, CurveName(..), Curve(..), CurvePrime(..), CurveCommon(..))
#else
import qualified Crypto.PubKey.ECC.P256 as P256
#endif

import           Basement.Imports (Natural)
import           Basement.Compat.CallStack
import           Foundation.Check (Arbitrary(..), Gen)

data KeyPair = KeyPair
    { toPrivateKey :: PrivateKey
    , toPublicKey  :: PublicKey
    }
    deriving (Show,Eq,Generic)

instance Binary KeyPair where
    put (KeyPair priv pub) = put priv >> put pub
    get = KeyPair <$> get <*> get

instance NFData KeyPair

newtype DhSecret = DhSecret ByteString
    deriving (Show,Eq,NFData,Binary)

keyFromBytes :: ByteString -> Scalar
keyFromBytes = keyFromNum . os2ip'
  where os2ip' :: ByteString -> Integer
        os2ip' = B.foldl' (\a b -> (256 * a) .|. (fromIntegral b)) 0

-- | Private Key
newtype PrivateKey = PrivateKey Scalar
    deriving (Show,Eq,NFData,Binary)

-- | Public Key
newtype PublicKey = PublicKey Point
    deriving (Show,Eq,NFData,Binary)

#ifdef OPENSSL

p256 :: SSL.EcGroup
p256 = maybe (error "p256 curve") id $ SSL.ecGroupFromCurveOID "1.2.840.10045.3.1.7"

newtype Point = Point { unPoint :: SSL.EcPoint }
    deriving (Generic)

instance SSize Point where
    type SizePoints Point = 1
    type SizeScalar Point = 0

instance NFData Point where
    rnf (Point p) = p `seq` ()

instance Show Point where
    show pnt@(Point p)
        | pointIsIdentity pnt = "Point Infinity"
        | otherwise           =
            let (x,y) = SSL.ecPointToAffineGFp p256 p
             in ("Point " ++ show x ++ " " ++ show y)
instance Eq Point where
    (Point a) == (Point b) = SSL.ecPointEq p256 a b
instance Binary Point where
    put = putByteString
        . flip (SSL.ecPointToOct p256) SSL.PointConversion_Compressed
        . unPoint
    get = either fail (return . Point) . SSL.ecPointFromOct p256 =<< getByteString 33

newtype Scalar = Scalar { unScalar :: Integer }
    deriving (Show,Eq,Generic,NFData)

instance SSize Scalar where
    type SizePoints Scalar = 0
    type SizeScalar Scalar = 1
instance Binary Scalar where
    put s = putByteString (scalarToBinary s)
    get = keyFromBytes <$> getByteString 32

scalarToBinary :: Scalar -> ByteString
scalarToBinary (Scalar i) = i2ospOf_ 32 i

keyFromNum :: Integer -> Scalar
keyFromNum n = Scalar (n `mod` SSL.ecGroupGetOrder p256)

keyInverse :: Scalar -> Scalar
keyInverse (Scalar 0) = Scalar 0
keyInverse (Scalar a) = Scalar $ recipModInteger a order
  where
    order = SSL.ecGroupGetOrder p256

keyNegate :: Scalar -> Scalar
keyNegate (Scalar x) = Scalar (order - x)
  where
    order = SSL.ecGroupGetOrder p256

keyGenerate :: MonadRandom randomly => randomly Scalar
keyGenerate = Scalar <$> generateMax order
  where
    order = SSL.ecGroupGetOrder p256

keyPairGenerate :: MonadRandom randomly => randomly KeyPair
keyPairGenerate = do
    k <- keyGenerate
    return $ KeyPair (PrivateKey k) (PublicKey $ pointFromSecret k)

pointToDhSecret :: Point -> DhSecret
pointToDhSecret (Point p) =
    let (x, _) = SSL.ecPointToAffineGFp p256 p
     in DhSecret $ B.convert $ hashSHA256 $ i2ospOf_ 32 x

pointFromX :: HasCallStack => Integer -> Maybe Point
pointFromX x
    | legendre yp2 p == 1 = exceptionRethrow ("pointFromX " ++ show x ++ show my) ((\(y,_) -> Point $ SSL.ecPointFromAffineGFp p256 (x,y)) <$> my)
    | otherwise           = Nothing
  where
    my   = tonelliShanks yp2 p
    (CurveFP (CurvePrime p cc)) = getCurveByName SEC_p256r1
    --cc  = common_curve curve
    a   = ecc_a cc
    b   = ecc_b cc
    yp2 = (x ^ (3 :: Int) + a * x + b) `mod` p

exceptionRethrow :: HasCallStack => String -> a -> a
exceptionRethrow s f = unsafePerformIO $ do
    (evaluate f) `catch` (\(e :: SomeException) -> error ("while doing : " ++ s ++ " : " ++ show e))

-- | calculate legendre symbol
--
-- p need to be an odd prime
legendre :: Integer -> Integer -> Integer
legendre a p = expFast a ((p-1) `div` 2) p

-- | Calculate the square mod p
sqrmod :: Integer -> Integer -> Integer
sqrmod a p = (a * a) `mod` p

-- | Calculate sqrt of n mod p using tonelli-shanks
tonelliShanks :: Integer -> Integer -> Maybe (Integer, Integer)
tonelliShanks n p
    | s == 1    = let r = expFast n ((p+1) `div` 4) p in vrfy (r, p-r)
    | otherwise =
        let z = findZ 2
            c = expFast z q p
            r = expFast n ((q+1) `div` 2) p
            t = expFast n q p
            m = s
         in loop r c t m

  where
    vrfy xs@(x1,_) | sqrmod x1 p == n = Just xs
                   | otherwise        = Nothing
    loop !r !c !t !m
        | (t `mod` p) == 1 = vrfy (r, p - r)
        | otherwise        =
            let t2 = sqrmod t p
                i  = findI t2 m
                b  = expFast c (2 ^ (m - i - 1)) p
                b2 = sqrmod b p
             in loop ((r * b) `mod` p)
                     b2
                     ((t * b2) `mod` p)
                     i

    -- find the lowest i, 0 < i < m, such that t^(2^i) = 1 (mod p)
    findI t2 m = find 1
      where find !i
                | i == m                  = i
                | ((t2 ^ i) `mod` p) == 1 = i
                | otherwise               = find (i+1)

    q :: Integer
    s :: Int
    (q, s) = div2 0 (p-1)
    div2 is iq
        | even iq   = div2 (is+1) (iq `shiftR` 1)
        | otherwise = (iq, is)

    -- find the lowest Z that is not a residue mod p
    findZ !z
        | legendre 2 p == -1 = z
        | otherwise          = findZ (z+1)

pointToX :: HasCallStack => Point -> Integer
pointToX pnt@(Point p)
    | pointIsIdentity pnt = error "pointToX: point to infinity"
    | otherwise           = fst $ SSL.ecPointToAffineGFp p256 p

pointFromSecret :: Scalar -> Point
pointFromSecret (Scalar s) = Point $ SSL.ecPointGeneratorMul p256 s

pointIdentity :: Point
pointIdentity = Point $ SSL.ecPointInfinity p256

pointIsIdentity :: Point -> Bool
pointIsIdentity (Point p) = SSL.ecPointIsAtInfinity p256 p

pointToBinary :: Point -> ByteString
pointToBinary = flip (SSL.ecPointToOct p256) SSL.PointConversion_Compressed . unPoint

hashUpdatePoints :: Context SHA256 -> [Point] -> Context SHA256
hashUpdatePoints ctx = foldl' (\c -> hashUpdate c . pointToBinary) ctx

hashFinalizeScalar :: Context SHA256 -> Scalar
hashFinalizeScalar = keyFromBytes . B.convert . hashFinalize

hashPoints :: [Point] -> ByteString
hashPoints elements =
    B.convert $ hashSHA256 $ mconcat $ fmap pointToBinary elements

hashPointsToKey :: [Point] -> Scalar
hashPointsToKey elements =
    keyFromBytes $ B.convert $ hashSHA256 $ mconcat
                 $ fmap pointToBinary elements

curveGenerator :: Point
curveGenerator = Point $ SSL.ecGroupGetGenerator p256

-- | Point adding
(.+) :: Point -> Point -> Point
(.+) (Point a) (Point b) = Point (SSL.ecPointAdd p256 a b)

-- | Point subtraction
(.-) :: Point -> Point -> Point
(.-) (Point a) (Point b) = Point (SSL.ecPointAdd p256 a $ SSL.ecPointInvert p256 b)

-- | Point scaling
(.*) :: Point -> Scalar -> Point
(.*) (Point a) (Scalar s) = Point (SSL.ecPointMul p256 a s)

-- | Point scaling, flip (*.)
(*.) :: Scalar -> Point -> Point
(*.) (Scalar s) (Point a) = Point (SSL.ecPointMul p256 a s)

(#+) :: Scalar -> Scalar -> Scalar
(#+) (Scalar a) (Scalar b) = keyFromNum (a + b)

(#-) :: Scalar -> Scalar -> Scalar
(#-) (Scalar a) (Scalar b) = keyFromNum (a - b)

(#*) :: Scalar -> Scalar -> Scalar
(#*) (Scalar a) (Scalar b) = keyFromNum (a * b)

infixl 7 #*
infixl 6 #+
infixl 6 #-

(#^) :: Scalar -> Natural -> Scalar
(#^) (Scalar a) n =
    Scalar $ expFast a (fromIntegral n) order
  where
    order = SSL.ecGroupGetOrder p256

mulAndSum :: [(Point,Scalar)] -> Point
mulAndSum l = Point $ SSL.ecPointsMulAndSum p256 (map (\(Point p, Scalar s) -> (p, s)) l)

mulPowerAndSum :: [Point] -> Integer -> Point
mulPowerAndSum l n = Point $ SSL.ecPointsMulOfPowerAndSum p256 (map unPoint l) n

#else
newtype Point = Point { unPoint :: P256.Point }
    deriving (Show,Eq)

newtype Scalar = Scalar P256.Scalar
    deriving (Eq)

instance Show Scalar where
    show (Scalar p) = show (P256.scalarToInteger p)

p256Mod :: Integer
p256Mod = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

curveGenerator :: Point
curveGenerator = pointIdentity

pointFromSecret :: Scalar -> Point
pointFromSecret (Scalar s) = Point $ P256.toPoint s

pointToDhSecret :: Point -> DhSecret
pointToDhSecret (Point p) = DhSecret $ B.convert $ hashSHA256 $ P256.pointToBinary p

-- | Point adding
(.+) :: Point -> Point -> Point
(.+) (Point a) (Point b) = Point (P256.pointAdd a b)

-- | Point scaling
(.*) :: Point -> Scalar -> Point
(.*) (Point a) (Scalar s) = Point (P256.pointMul s a)

-- | Point scaling, flip (*.)
(*.) :: Scalar -> Point -> Point
(*.) (Scalar s) (Point a) = Point (P256.pointMul s a)

(#+) :: Scalar -> Scalar -> Scalar
(#+) (Scalar a) (Scalar b) = Scalar (P256.scalarAdd a b)

(#-) :: Scalar -> Scalar -> Scalar
(#-) (Scalar a) (Scalar b) = Scalar (P256.scalarSub a b)

(#*) :: Scalar -> Scalar -> Scalar
(#*) (Scalar a) (Scalar b) =
    Scalar $ throwCryptoError $ P256.scalarFromInteger ((an * bn) `mod` p256Mod)
  where
    an = P256.scalarToInteger a
    bn = P256.scalarToInteger b

(#^) :: Scalar -> Natural -> Scalar
(#^) (Scalar a) n =
    Scalar $ throwCryptoError
           $ P256.scalarFromInteger
           $ expSafe (P256.scalarToInteger a) (fromIntegral n) p256Mod

pointIdentity :: Point
pointIdentity = Point $ P256.pointFromIntegers 0 0

keyFromNum :: Integer -> Scalar
keyFromNum = Scalar . throwCryptoError . P256.scalarFromInteger

keyInverse :: Scalar -> Scalar
keyInverse (Scalar s) = Scalar (P256.scalarInv s)

keyGenerate :: MonadRandom randomly => randomly Scalar
keyGenerate = Scalar <$> P256.scalarGenerate

keyPairGenerate :: MonadRandom randomly => randomly KeyPair
keyPairGenerate = do
    k <- keyGenerate
    return $ KeyPair k (pointFromSecret k)

hashPointsToKey :: [Point] -> Scalar
hashPointsToKey elements =
    keyFromBytes $ B.convert $ hashSHA256 $ mconcat $ fmap (P256.pointToBinary . unPoint) elements

#endif

hashSHA256 :: ByteString -> Digest SHA256
hashSHA256 m = hash m

instance Arbitrary Scalar where
    arbitrary = arbitraryScalar
instance Arbitrary Point where
    arbitrary = arbitraryPoint

arbitraryScalar :: Gen Scalar
arbitraryScalar = arbitrary >>= \drg -> pure $ fst (withDRG (drgNewTest drg) keyGenerate)

arbitraryPoint :: Gen Point
arbitraryPoint = pointFromSecret <$> arbitraryScalar
