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
module Crypto.Casino.ZKSH.Operations where

import           Basement.Nat
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
import           Crypto.Casino.Primitives.HelperListN (rewriteListN_M1P1)
import           Crypto.Random
import           Crypto.Casino.Primitives.ECC
import           Crypto.Casino.Primitives.Matrix
import qualified Crypto.Casino.Primitives.Matrix as Matrix
import           Crypto.Casino.Primitives.TEG (Random)
import           Prelude hiding (product)

-- | Create a list of size X of random values
randoms :: forall x randomly . (KnownNat x, NatWithinBound Int x, MonadRandom randomly)
        => randomly (ListN x Random)
randoms = ListN.replicateM @x keyGenerate

innerProduct :: ListN n Scalar -> ListN n Scalar -> Scalar
innerProduct a b = foldl (#+) (keyFromNum 0) $ ListN.unListN $ ListN.zipWith (#*) a b

sumScalar :: [Scalar] -> Scalar
sumScalar l = foldl1 (#+) l

sumScalarN :: (1 <= x) => ListN x Scalar -> Scalar
sumScalarN = ListN.foldl1' (#+)

productScalar :: [Scalar] -> Scalar
productScalar l = foldl1 (#*) l

-- | Scale a vector of size n
(*|) :: Scalar -> ListN n Scalar -> ListN n Scalar
(*|) v = ListN.map (#* v)

-- | Sum 2 vectors of size n
(|+|) :: ListN n Scalar -> ListN n Scalar -> ListN n Scalar
(|+|) = ListN.zipWith (#+)

(|*|) :: (Matrix.DimensionsValid n m, Matrix.DimensionsValid m 1, Matrix.DimensionsValid n 1)
      => ListN n (ListN m Scalar) -> ListN m Scalar -> ListN n Scalar
(|*|) x y = Matrix.getCol 0 r
  where
    r = Matrix.mul (ListN.foldl1' (#+))
               (#*)
               (Matrix.fromRows x)
               (Matrix.fromCols (ListN.singleton y))

(|.+|) :: ListN n Point -> ListN n Point -> ListN n Point
(|.+|) = ListN.zipWith (.+)

(|-|) :: ListN n Scalar -> ListN n Scalar -> ListN n Scalar
(|-|) = ListN.zipWith (#-)

(|.*|) :: ListN x Point -> Scalar -> ListN x Point
(|.*|) l e = ListN.map (\p -> p .* e) l

infixl 7 *|
infixl 6 |+|
infixl 6 |-|

vectorNegate :: ListN n Scalar -> ListN n Scalar
vectorNegate = ListN.map (\p -> keyNegate p)

vectorProduct :: ListN n Scalar -> Scalar
vectorProduct = ListN.foldl (#*) (keyFromNum 1)

matrixHadamardSum :: Matrix m n Scalar -> Matrix m n Scalar -> Scalar
matrixHadamardSum (Matrix a) (Matrix b) = ListN.foldl' (#+) (keyFromNum 0) $ hadamard a b

hadamard :: ListN n Scalar -> ListN n Scalar -> ListN n Scalar
hadamard = ListN.zipWith (#*)

-- compute x vector = { x^1, x^2, ..., x^N }
exponentsOfX :: (NatWithinBound Int o, KnownNat o) => Scalar -> ListN o Scalar
exponentsOfX x = -- ListN.create (\i -> x #^ (i+1))
    ListN.scanl1' (#*) (ListN.replicate x)

exponentsOfXFrom1 :: forall o . (1 <= o, NatWithinBound Int o, KnownNat o) => Scalar -> ListN o Scalar
exponentsOfXFrom1 x =
    rewriteListN_M1P1 (keyFromNum 1 `ListN.cons` ListN.init (exponentsOfX @o x))

extendSingletonWithZero :: KnownNat n => Scalar -> ListN n Scalar
extendSingletonWithZero v = ListN.create $ \i -> if i == 0 then v else keyFromNum 0
