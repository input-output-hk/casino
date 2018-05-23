-- a generic matrix type + helpers
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE BangPatterns  #-}
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
-- TODO move to NormalForm, once gauge get support
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Crypto.Casino.Primitives.Matrix
    ( DimensionsValid
    , Matrix(..)
    , mapRows
    , mapCols
    , getRow
    , getCol
    , fromList
    , fromRows
    , fromCols
    , toRows
    , toCols
    , get
    , allDiagonals
    , prependRow
    , appendRow
    , foldRows
    , add
    , map
    , mul
    ) where

import           Basement.Nat
import           Basement.Types.OffsetSize
import           Foundation.Check (Arbitrary(..))
import           Control.DeepSeq
import           Data.Proxy
import           GHC.Generics
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN
import qualified Crypto.Casino.Primitives.HelperListN as LH (group, unGroup, transpose)
import           Crypto.Casino.Primitives.SSize
import           Prelude hiding (map)
import qualified Prelude

-- | A Constraint for valid dimensions for a Matrix type
type DimensionsValid rows cols =
    ( NatWithinBound Int rows, KnownNat rows
    , NatWithinBound Int cols, KnownNat cols
    , NatWithinBound Int (rows * cols), KnownNat (rows * cols)
    , 1 <= rows, 1 <= cols
    )

-- | Matrix types
newtype Matrix (rows :: Nat) (cols :: Nat) a = Matrix { toList :: ListN (rows * cols) a }
    deriving (Show,Eq,Generic)

instance (Arbitrary a, DimensionsValid m n) => Arbitrary (Matrix m n a) where
    arbitrary = Matrix <$> ListN.replicateM arbitrary

instance NFData a => NFData (ListN n a)
instance NFData a => NFData (Matrix rows cols a)

instance SSize a => SSize (Matrix m n a) where
    type SizePoints (Matrix m n a) = m * n * SizePoints a
    type SizeScalar (Matrix m n a) = m * n * SizeScalar a

-- | Map all row elements to a 'b' and output the list of rows associated
mapRows :: forall rows cols a b .
           (DimensionsValid rows cols)
        => (ListN cols a -> b) -> Matrix rows cols a -> ListN rows b
mapRows f (Matrix l) = ListN.map f $ LH.group l

-- | Map all columns elements to a 'b' and output the list of cols associated
mapCols :: forall rows cols a b .
           (DimensionsValid rows cols)
        => (ListN rows a -> b) -> Matrix rows cols a -> ListN cols b
mapCols f (Matrix l) = ListN.map f $ LH.transpose $ LH.group l

-- | Get a specific     row from the matrix given by an offset starting at 0
getRow :: forall rows cols a . DimensionsValid rows cols
       => Word               -- ^ The row to get, starting at offset 0
       -> Matrix rows cols a -- ^ The matrix to address
       -> ListN cols a       -- ^ The row demanded of size 'cols'
getRow n mat = ListN.index (toRows mat) (Offset $ fromIntegral n)

-- | Get a specific column from the matrix given by an offset starting at 0
getCol :: forall rows cols a . DimensionsValid rows cols
       => Word               -- ^ The column to get, starting at offset 0
       -> Matrix rows cols a -- ^ The matrix to address
       -> ListN rows a       -- ^ The column demanded of size 'rows'
getCol n mat = ListN.index (toCols mat) (Offset $ fromIntegral n)

-- | Create a matrix from all the value express in a list starting from
-- the first row to the last
fromList :: (rows * cols) ~ l => ListN l a -> Matrix rows cols a
fromList = Matrix

-- | Create a matrix from a list of rows
fromRows :: forall rows cols a .
            (DimensionsValid rows cols)
         => ListN rows (ListN cols a) -> Matrix rows cols a
fromRows = Matrix . LH.unGroup

-- | Create a matrix from a list of columns
fromCols :: forall rows cols a .
            (DimensionsValid rows cols)
         => ListN cols (ListN rows a) -> Matrix rows cols a
fromCols = Matrix . LH.unGroup . LH.transpose

-- | Convert a matrix to a list of rows
toRows :: forall rows cols a . ( DimensionsValid rows cols )
        => Matrix rows cols a
        -> ListN rows (ListN cols a)
toRows (Matrix content) = LH.group content

-- | Convert a matrix to a list of columns
toCols :: forall rows cols a . ( DimensionsValid rows cols )
        => Matrix rows cols a
        -> ListN cols (ListN rows a)
toCols (Matrix content) = LH.transpose $ LH.group content

-- | Get one specific element of a matrix
get :: forall rows cols a . ( DimensionsValid rows cols )
    => Matrix rows cols a
    -> Offset a
    -> Offset a
    -> a
get (Matrix content) (Offset row) (Offset col) =
    ListN.index content $ Offset (row * rowSize + col)
  where
    rowSize = natValInt (Proxy @rows)

-- | Add element of 2 matrix given an operation
add :: (a -> a -> a)
    -> Matrix rows cols a
    -> Matrix rows cols a
    -> Matrix rows cols a
add op (Matrix a) (Matrix b) = Matrix $ ListN.zipWith op a b

-- | Map all elements of a matrix
map :: (a -> b)
    -> Matrix rows cols a
    -> Matrix rows cols b
map f (Matrix a) = Matrix $ ListN.map f a

-- | Do a matrix multiplication parametrized by the product operation
-- and the reduce operation
mul :: forall m n p a b c .
       (DimensionsValid m n, DimensionsValid n p, DimensionsValid m p)
    => (ListN n c -> c) -- ^ reduce step (e.g. addition)
    -> (a -> b -> c)    -- ^ element product operation
    -> Matrix m n a     -- ^ Left matrix
    -> Matrix n p b     -- ^ Right matrix
    -> Matrix m p c     -- ^ Resulting matrix
mul reduce op a b =
    fromRows $ ListN.map (\r -> ListN.map (\c -> reduce $ ListN.zipWith op r c) cols)
              (toRows a)
  where
    !cols = toCols b

-- | Return a list of all possible diagonals, starting from
-- the bottom left corner (1 element), ending at the top right corner (1 element)
allDiagonals :: forall m n a .
                ( KnownNat m
                , KnownNat n
                , KnownNat (2 * m - 1)
                , NatWithinBound Int (2 * m - 1))
             => Matrix m n a -> ListN (2 * m - 1) [a]
allDiagonals (Matrix (ListN.unListN -> l)) =
    maybe (error "allDiagonals") id $ ListN.toListN @ (2 * m - 1) $ Prelude.map (Prelude.map toValue) diags
  where
    toValue :: (Int, Int) -> a
    toValue pos = l !! rowColToIndex pos
    rows = fromIntegral $ natVal (Proxy @m)
    cols = fromIntegral $ natVal (Proxy @n)
    rowColToIndex (r,c) = r     * rows + c
    startingPoints = [ (i, 0) | i <- [1..rows-1] ]
                  ++ [ (0, j) | j <- [0..cols-1] ]
    diags :: [[(Int, Int)]]
    diags = [ [ (x+i, y+i)
              | i <- [0..rows], x+i < rows, y+i < cols
              ]
            | (x,y) <- startingPoints ]

prependRow :: forall m n a . (DimensionsValid m n, DimensionsValid (m+1) n)
           => ListN n a        -- ^ row to prepend
           -> Matrix m n a     -- ^ matrix
           -> Matrix (m+1) n a -- ^ resulting matrix
prependRow row (Matrix m) =
    maybe (error "prependRow") Matrix $ ListN.toListN @((m+1) * n) (ListN.unListN row ++ ListN.unListN m)

appendRow :: forall m n a . (DimensionsValid m n, DimensionsValid (m+1) n)
          => Matrix m n a     -- ^ matrix
          -> ListN n a        -- ^ row to append
          -> Matrix (m+1) n a -- ^ resulting matrix
appendRow (Matrix m) row =
    maybe (error "appendRow") Matrix $ ListN.toListN @((m+1) * n) (ListN.unListN m ++ ListN.unListN row)

foldRows :: DimensionsValid m n
         => (ListN n a -> ListN n a -> ListN n a)
         -> Matrix m n a
         -> ListN n a
foldRows f = ListN.foldl1' f . toRows
