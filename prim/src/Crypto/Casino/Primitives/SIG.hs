{-# LANGUAGE NoImplicitPrelude #-}
module Crypto.Casino.Primitives.SIG
    ( SigningKey
    , VerifyKey
    , Signature
    , Message
    , generate
    , sign
    , verify
    ) where

import           Crypto.Random
import           Crypto.Hash (SHA256(..))
import qualified Crypto.PubKey.ECC.ECDSA as ECDSA -- TODO: replace by openssl module
import qualified Crypto.PubKey.ECC.Types as ECC
import qualified Crypto.PubKey.ECC.Prim as ECC
import           Basement.UArray (UArray)
import           Basement.Imports

type SigningKey = ECDSA.PrivateKey
type VerifyKey = ECDSA.PublicKey
type Signature = ECDSA.Signature
type Message = UArray Word8

generate :: MonadRandom randomly => randomly (SigningKey, VerifyKey)
generate = do
    k <- ECC.scalarGenerate curve
    let point = ECC.pointBaseMul curve k
        kp    = ECDSA.KeyPair curve point k
    pure (ECDSA.toPrivateKey kp, ECDSA.toPublicKey kp)
  where
    -- n = ECC.ecc_n . ECC.common_curve $ private_curve pk
    curve = ECC.getCurveByName ECC.SEC_p256r1
 
sign :: MonadRandom randomly => SigningKey -> Message -> randomly Signature
sign sk msg = ECDSA.sign sk SHA256 msg

verify :: VerifyKey -> Message -> Signature -> Bool
verify vk msg sig = ECDSA.verify SHA256 vk sig msg
