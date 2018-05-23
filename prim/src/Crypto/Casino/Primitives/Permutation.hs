{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
module Crypto.Casino.Primitives.Permutation
    ( Permutation
    , toList
    , identity
    , export
    , combine
    , randomize
    , apply
    , tests
    ) where

import           Basement.Nat
import           Basement.UArray (UArray)
import           Basement.Imports (Natural)
import           Data.Proxy
import           Data.Word
import           GHC.Generics (Generic)
import           Control.DeepSeq
import           Crypto.Random
import           Crypto.Number.Serialize (os2ip)
import           Foundation.Check
import           Foundation.List.ListN (ListN)
import qualified Foundation.List.ListN as ListN

-- | Permutation of an order sequence of n-value 0-based
newtype Permutation (n :: Nat) = Permutation { toList :: ListN n Natural }
    deriving (Show,Eq,Generic)

instance NFData (Permutation n) where
    rnf (Permutation l) = rnf (ListN.unListN l)

instance (KnownNat n, NatWithinBound Int n) => Arbitrary (Permutation n) where
    arbitrary = arbitrary >>= \drg -> pure $ fst (withDRG (drgNewTest drg) (randomize identity))

-- | The identity permutation which doesn't change anything when applied
--
-- identity = { 0, 1, .., n }
identity :: KnownNat n => Permutation n
identity = Permutation $ ListN.create id

-- | Export the permutation list on a 1-to-n indexing system.
--
-- to rebase to a 0-indexing, 1 need to be subtracted to each element.
export :: (Natural -> a) -> Permutation n -> ListN n a
export f (Permutation l) = ListN.map (f . (+1)) l

-- | Combine 2 permutations by applying the first permutation and the second one
--
-- The following rules should apply:
-- > apply perm1 . apply perm2 === apply (combine perm1 perm2)
combine :: forall n . (KnownNat n, NatWithinBound Int n)
        => Permutation n
        -> Permutation n
        -> Permutation n
combine (Permutation (ListN.unListN -> a)) (Permutation (ListN.unListN -> b)) =
    Permutation $ maybe (error "combine: impossible") id
                $ ListN.toListN
                $ map (\i -> b !! naturalToIndex (a !! i)) [0..natValInt (Proxy @n)]

randomize :: (MonadRandom randomly, NatWithinBound Int n, KnownNat n)
          => Permutation n -> randomly (Permutation n)
randomize (Permutation (ListN.unListN -> l)) =
    Permutation . maybe (error "randomize: impossible") id
                . ListN.toListN
              <$> loop [] l
  where
    loop acc []      = pure (reverse acc)
    loop acc [x]     = pure (reverse $ x:acc)
    loop acc current = do
        let m = length current
        v <- fromIntegral . os2ip @(UArray Word8) <$> getRandomBytes 8
        -- TODO: mod BIAS here. remove with buckets
        let p = current !! (v `mod` m)
            next = filter (/= p) current
        loop (p : acc) next

-- | Apply the permutation to a list of element, returning the permuted list
--
-- > apply (Permutation [2,0,1]) [10,20,30]
-- > [30,10,20]
apply :: (KnownNat n, NatWithinBound Int n) => Permutation n -> ListN n a -> ListN n a
apply (Permutation perms) (ListN.unListN -> l) =
    ListN.map (\p -> l !! naturalToIndex p) perms

naturalToIndex :: Natural -> Int
naturalToIndex = fromIntegral

tests :: Test
tests = Group "permutations"
    [ Property "identity" $ \(l :: ListN 16 Int) -> apply identity l == l
    , Property "randomize" $ \(l :: ListN 24 Int) (p :: Permutation 24) ->
        if p == identity then True else apply p l /= l
    , Property "apply + apply == id" $ \(l :: ListN 24 Int) (p :: Permutation 24) ->
        apply p (apply p l) == l
    ]
