{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Crypto.Casino.Primitives.SSize
    where

import GHC.TypeLits
import qualified Basement.Sized.List as ListN

class SSize a where
    type SizePoints a :: Nat
    type SizeScalar a :: Nat

instance SSize a => SSize (ListN.ListN n a) where
    type SizePoints (ListN.ListN n a) = n * SizePoints a
    type SizeScalar (ListN.ListN n a) = n * SizeScalar a
