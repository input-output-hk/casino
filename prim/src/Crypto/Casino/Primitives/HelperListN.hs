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
module Crypto.Casino.Primitives.HelperListN
    where

import           Basement.Nat
import           Basement.Types.OffsetSize (Offset(..))
import           Data.Proxy
import           Basement.Sized.List (ListN)
import qualified Basement.Sized.List as ListN

import           GHC.Prim

group :: forall rows cols l a .
         ( (rows * cols) ~ l
         , NatWithinBound Int cols, KnownNat cols
         , NatWithinBound Int rows, KnownNat rows)
      => ListN l a
      -> ListN rows (ListN cols a)
group = ListN.toListN_ @rows
      . map (ListN.toListN_ @cols)
      . loop (natValInt (Proxy @cols))
      . ListN.unListN
  where
    loop _ [] = []
    loop v l  = let (l1,l2) = splitAt v l in l1 : loop v l2

unGroup :: (NatWithinBound Int l, KnownNat l, (rows * cols) ~ l) => ListN rows (ListN cols a) -> ListN l a
unGroup l =
    ListN.toListN_ $ concat $ ListN.unListN $ ListN.map ListN.unListN l

transpose :: (NatWithinBound Int cols, KnownNat cols)
          => ListN rows (ListN cols a)
          -> ListN cols (ListN rows a)
transpose l = ListN.map (\i -> ListN.map (getAt i) l) range
  where
    getAt i x = ListN.index x (Offset i)

-- | Create a list from 0 to N-1 of N elements
range :: forall n . (NatWithinBound Int n, KnownNat n) => ListN n Int
range = ListN.toListN_ [0..(natValInt (Proxy @n) - 1)]

-- | Consider the list as a queue, and pop the head and push an element to the end
--
-- > pushPop [1,2,3] 4
-- [2,3,4]
pushPop :: forall n a . (1 <= n, NatWithinBound Int n, KnownNat n) => ListN n a -> a -> ListN n a
-- pushPop (ListN.unListN -> l) a = ListN.toListN_ (tail l ++ [a])
pushPop l a = rewriteListN_M1P1 (ListN.tail l `ListN.snoc` a)

-- | merge 2 list of the same size by interspersing elements
--
-- > mergeIntersperse [1,3,5] [2,4,6]
-- [1,2,3,4,5,6]
mergeIntersperse :: forall n a . (NatWithinBound Int n, KnownNat n, NatWithinBound Int (n+n), KnownNat (n+n))
                 => ListN n a -> ListN n a -> ListN (n+n) a
mergeIntersperse (ListN.unListN -> l1) (ListN.unListN -> l2) =
    ListN.toListN_ $ concat $ zipWith (\x y -> [x,y]) l1 l2

rewriteListN_M1P1 :: 1 <= x => ListN ((x-1)+1) a -> ListN x a
rewriteListN_M1P1 = coerce

rewriteListN_P1M1 :: ListN ((x+1)-1) a -> ListN x a
rewriteListN_P1M1 = coerce
