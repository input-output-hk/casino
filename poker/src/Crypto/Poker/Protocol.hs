{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}
module Crypto.Poker.Protocol
    where

import           GHC.TypeLits
import           Crypto.Random
import           Data.Proxy
import           Basement.Nat
import           Basement.Bounded
import           Basement.Compat.Natural
import           Basement.Compat.Bifunctor
import           Basement.String (lower)
import           Foundation.List.ListN (ListN)
import qualified Foundation.List.ListN as ListN
import           Foundation.Collection

import qualified Crypto.Casino.Primitives.TEG as TEG
import qualified Crypto.Casino.Primitives.SIG as SIG
import qualified Crypto.Casino.Primitives.Commitment as Commitment

import           Crypto.Casino.ZKSH (ShuffleProof)
import           Crypto.Poker.Card
import           Crypto.Poker.Game
import           Crypto.Poker.Ledger (Ledger)
import qualified Crypto.Poker.Ledger as Ledger

import           Foundation
import qualified Prelude

data RoundStatus = SetStatus PlayerStatus | Betting | NotBetYet
    deriving (Show,Eq)

data PlayerStatus = Folded | IsAllIn | Active
    deriving (Show,Eq)

-- | Public Player game state
data Player = Player
    { totalBet :: Amount
    , balance  :: Amount
    , active   :: PlayerStatus
    , identity :: PlayerIdentity
    }
    deriving (Show,Eq)

data PlayerCurrentBet = PlayerCurrentBet
    { status :: RoundStatus
    , bet    :: Amount
    } deriving (Show,Eq)

-- | The overall game state, including our own player specific game state
-- that is hidden to other player
data GameST n = GameST
    { stLedger         :: Ledger (Event Operation)
    , stPid            :: Maybe PlayerNumber
    , stPlayer         :: ListN n Player
    , stRng            :: ChaChaDRG
    }

data HandSetup n = HandSetup
    { handJointKey      :: TEG.JointPublicKey
    , handCommitmentKey :: Commitment.CommitmentKey ShuffleCols
    , handPlayerPubs    :: ListN n TEG.PublicKey
    , handPlayerVKs     :: ListN n SIG.VerifyKey
    }

-- | Cryptographic material own player
data PrivateInformation = PrivateInformation
    { privateSigning :: !SIG.SigningKey
    , privateSecret  :: !TEG.SecretKey
    , privatePublic  :: (SIG.VerifyKey, TEG.PublicBroadcast)
    } deriving (Show,Eq)

generatePrivateInformation :: MonadRandom randomly => randomly PrivateInformation
generatePrivateInformation = mk <$> SIG.generate <*> TEG.generation
  where mk (sig, vrf) (pub, sec) =
            PrivateInformation
                { privateSigning = sig
                , privateSecret  = sec
                , privatePublic  = (vrf, pub)
                }

initialPlayer :: InitialStake -> Player
initialPlayer bal = Player { totalBet = 0
                           , balance  = bal
                           , active   = undefined
                           , identity = 10
                           }

initialPlayerCurrentBet :: PlayerCurrentBet
initialPlayerCurrentBet = PlayerCurrentBet
    { status = NotBetYet
    , bet    = 0
    }

initialGameST :: ValidNbPlayers n => InitialStake -> ChaChaDRG -> GameST n
initialGameST stake rng = GameST
    { stLedger         = Ledger.empty
    , stPid            = Nothing
    , stPlayer         = ListN.replicate (initialPlayer stake)
    , stRng            = rng
    }

-- 5 community cards + 2 cards per players < NbCards
--
-- Many constraints specified here are redundant,
-- since the compiler cannot work out basic logic assumptions.
type ValidNbPlayers n =
    ( 2 <= n
    , (n <=? MaxPlayers) ~ 'True
    , KnownNat (n-1)
    , KnownNat n
    , NatWithinBound Int (n+n)
    , NatWithinBound Int ((n-1)+(n-1))
    , n+n <= NbCards
    , KnownNat (n+n)
    , NatWithinBound Int (n-1)
    , NatWithinBound Int n
    , NatWithinBound (CountOf EncryptedCard) (n+n)
    )

type NumberOfPlayers = Nat
type Amount = Natural

type PlayerIdentity = Int     -- TODO Public Key
type SmallBlind = Amount      -- sb
type BigBlind = Amount        -- bb
type InitialStake = Amount    -- t
type MaximumBet = Amount      -- m
type SecurityDeposit = Amount -- d
type Compensation = Amount    -- q

data CheckinMessage = CheckinMessage Amount
    deriving (Show,Eq)

newtype EncryptedCard = EncryptedCard { encryptedCardCT :: TEG.Ciphertext }
    deriving (Eq)
instance Prelude.Show EncryptedCard where
   show (EncryptedCard c) = "E" <> TEG.debugHash c

pokerStart :: Poker n a -> GameST n -> Result Operation GameST n a
pokerStart p st = runPoker p st (\_ s -> Failed s) Ok

newtype Poker n a = Poker
    { runPoker :: forall a'
                . GameST n
               -> Failure Operation GameST n a'
               -> Success Operation GameST n a a'
               -> Result Operation GameST n a'
    }

instance Functor (Poker n) where
    fmap f fa = Poker $ \st0 err ok ->
        runPoker fa st0 err $ \st1 a -> ok st1(f a)
    {-# INLINE fmap #-}

instance Applicative (Poker n) where
    pure a = Poker $ \buf _ ok -> ok buf a
    {-# INLINE pure #-}
    fab <*> fa = Poker $ \st0 err ok ->
        runPoker fab st0 err $ \st1 ab ->
        runPoker fa  st1 err $ \st2 ->
            ok st2 . ab
    {-# INLINE (<*>) #-}

instance Monad (Poker n) where
    return = pure
    {-# INLINE return #-}
    m >>= k       = Poker $ \st0 err ok ->
        runPoker  m    st0  err $ \st1 a ->
        runPoker (k a) st1 err ok
    {-# INLINE (>>=) #-}

instance MonadRandom (Poker n) where
    getRandomBytes n =
        modifyStateRet $ \st ->
            second (\rng -> st { stRng = rng }) $ randomBytesGenerate n (stRng st)

failed :: String -> Poker n a
failed s = Poker $ \st err _ -> err st s

expectJust :: String -> Maybe a -> Poker n a
expectJust cat Nothing  = failed (cat <> ": expect Just got Nothing")
expectJust _   (Just a) = pure a

expectLength :: String -> CountOf a -> [a] -> Poker n [a]
expectLength cat len l
    | length l == len = pure l
    | otherwise       = failed (cat <> ": expect list of length: " <> show len <> " but got: " <> show (length l))

withRng :: MonadPseudoRandom ChaChaDRG a -> Poker n a
withRng f =
    modifyStateRet $ \st -> do
        let (r, retRng) = withDRG (stRng st) f
         in (r, st { stRng = retRng })

modifyState :: (GameST n -> GameST n) -> Poker n ()
modifyState f = Poker $ \st _ ok -> ok (f st) ()

modifyStateRet :: (GameST n -> (a, GameST n)) -> Poker n a
modifyStateRet f = Poker $ \st _ ok -> let (a, st2) = f st in ok st2 a

modifyPlayer :: ValidNbPlayers n => PlayerNumber -> (Player -> Player) -> Poker n ()
modifyPlayer pid f = modifyState $ \st -> st { stPlayer = ListN.updateAt (pnToOffset pid) f (stPlayer st) }

getPlayer :: ValidNbPlayers n => PlayerNumber -> Poker n Player
getPlayer pid = getState (flip ListN.index (pnToOffset pid) . stPlayer)

pnToOffset :: PlayerNumber -> Offset a
pnToOffset pn = case Prelude.fromIntegral <$> pn - 1 of
    Nothing -> error "cannot convert player number to offset"
    Just n  -> Offset n

remove :: Eq a => a -> [a] -> [a]
remove _ [] = []
remove e (x:xs)
    | e == x    = xs
    | otherwise = x : remove e xs

getState :: (GameST n -> a) -> Poker n a
getState f = Poker $ \st _ ok -> ok st (f st)

getSelfId :: Poker n PlayerNumber
getSelfId = expectJust "player-id" =<< getState stPid

setSelfId :: PlayerNumber -> Poker n ()
setSelfId pid = modifyState $ \st -> st { stPid = Just pid }

isCurrentPlayer :: PlayerNumber -> Poker n Bool
isCurrentPlayer pid = (== pid) <$> getSelfId

isFirstPlayer :: Poker n Bool
isFirstPlayer = (== 1) <$> getSelfId

broadcast :: Operation -> Poker n ()
broadcast op = Poker $ \st1 _ ok -> Broadcast st1 op $ \st2 () -> ok st2 ()

fsc :: SIG.VerifyKey -> TEG.PublicBroadcast -> Poker n PlayerNumber
fsc vrf pub = Poker $ \st1 _ ok ->
    FSC st1 vrf pub $ \st2 pid -> ok st2 pid

debug :: String -> Poker n ()
debug s = Poker $ \st1 _ ok -> Debug st1 s $ \st2 () -> ok st2 ()

step :: String -> Poker n r -> Poker n r
step x f = debug ("START: " <> x) >> f >>= \r -> debug ("END:  " <> x) >> return r

userBet :: Poker n BettingAction
userBet = Poker $ \st1 err ok ->
    Input st1 "betting-action" $ \st2 r ->
        case lower r of
            "fold"   -> ok st2 FOLD
            "allin"  -> ok st2 ALLIN
            "call"   -> ok st2 CALL
            "check"  -> ok st2 CHECK
            s   | "raise " `isPrefixOf` s ->
                    -- TODO better error handling ...
                    let val = Prelude.read $ toList $ drop 6 s
                     in ok st2 $ RAISE val
                | otherwise -> err st2 ("unknown action: " <> r)

{-
adjustBalanceBet :: ValidNbPlayers n => PlayerNumber -> Amount -> Poker n ()
adjustBalanceBet pid am = do
    modifyPlayer pid $ \ply ->
        ply { bet     = bet ply + am
            , balance = adjustBalance ply
            }
  where
    adjustBalance ply = case balance ply - am of
        Nothing -> error "balance negative"
        Just b  -> b
-}

-- | Wait and Match for one event in the ledger
--
-- internal function, probably better to use wait, waitPrevious, waitAll, waitAllButMe
waitOne :: forall a n
         . String
        -> (Event Operation -> Maybe a)
        -> Poker n (Maybe a)
waitOne s f = Poker $ \st1 _ ok ->
    case Ledger.find (maybe False (const True) . f) (stLedger st1) of
        Nothing  ->
            Next st1 s $ \st2 pop ->
                let st3 = st2 { stLedger = Ledger.append pop (stLedger st2) }
                 in ok st3 (f pop)
        Just pop ->
            ok st1 (f pop)

-- | Wait for an event that have @f@ return a value.
wait :: forall a n
      . String
     -> (Event Operation -> Maybe a)
     -> Poker n a
wait s f = waitOne s f >>= maybe (wait s f) pure

-- | Wait for the previous player event
--
-- if the first player is calling this function,
-- then the event will be waited from the last player,
-- as typical card game round iterating from player on a round table.
waitPrevious :: forall a n
              . ValidNbPlayers n
             => String
             -> (Operation -> Maybe a)
             -> Poker n a
waitPrevious s f = do
    myId <- getSelfId
    let expectedPrevId = if myId == 1 then natValNatural (Proxy @n) else pred myId
    wait s $ \ev ->
        if isEventFromPlayer expectedPrevId ev
            then f (eventGetOperation ev)
            else Nothing

waitAll :: forall n a b
         . ValidNbPlayers n
        => String
        -> (Event Operation -> Maybe a)
        -> ([(PlayerNumber, a)] -> Poker n b)
        -> Poker n b
waitAll s f cb = allPlayerNumbers Proxy >>= \players -> waitPlayerList s players f cb

allPlayerNumbers :: forall n . ValidNbPlayers n => Proxy n -> Poker n [PlayerNumber]
allPlayerNumbers _ = pure [1..nbPlayers] where nbPlayers = natValNatural (Proxy @n)

allPlayerNumbersExceptMe :: forall n . ValidNbPlayers n => Poker n [PlayerNumber]
allPlayerNumbersExceptMe = do
    me <- getSelfId
    filter (/= me) <$> allPlayerNumbers Proxy

waitAllButMe :: forall n a b
              . ValidNbPlayers n
             => String
             -> (Event Operation -> Maybe a)
             -> ([(PlayerNumber, a)] -> Poker n b)
             -> Poker n b
waitAllButMe s f cb =
    allPlayerNumbersExceptMe >>= \players -> waitPlayerList s players f cb

data WaitFor = Wait | NoWait
    deriving (Show,Eq)

waitAllBut :: forall n a b . ValidNbPlayers n
    => String
    -> (PlayerNumber -> WaitFor) -- ^ player filtering function
    -> (Event Operation -> Maybe a)
    -> ([(PlayerNumber, a)] -> Poker n b)
    -> Poker n b
waitAllBut s filtering f cb = do
    plist <- filter (\pid -> case filtering pid of
                        Wait -> True
                        NoWait -> False) <$> allPlayerNumbers (Proxy @n)
    waitPlayerList s plist f cb

waitPlayerList :: forall n a b
         . ValidNbPlayers n
        => String
        -> [PlayerNumber] -- ^ the players to wait an event from
        -> (Event Operation -> Maybe a)
        -> ([(PlayerNumber, a)] -> Poker n b)
        -> Poker n b
waitPlayerList s players f cb = loop [] players
  where
    loop :: [(PlayerNumber, a)] -> [PlayerNumber] -> Poker n b
    loop acc [] = cb $ orderByPlayer acc
    loop acc l  = do
        r <- waitOne (s <> show l) $ \ev -> -- (pid, op) ->
                    let pid = eventGetPlayerNumber ev in
                    case f ev of
                        Just a  | elem pid l -> Just (pid, a)
                                | otherwise  -> Nothing -- probably a BUG ?
                        Nothing              -> Nothing
        case r of
            Nothing      -> loop acc l
            Just (pid,a) -> loop ((pid, a) : acc) (remove pid l)

    -- orderByPlayer :: [(PlayerNumber, a)] -> [a]
    orderByPlayer = sortBy (compare `on` fst)

-- | Operations being recorded on the private ledger
data Operation =
      CHECKIN (Checkin ShuffleCols)
    | SHUFFLED Natural (Deck NbCards EncryptedCard) (ShuffleProof ShuffleRows ShuffleCols)
    | SMALLBLIND
    | BIGBLIND
    | DRAW_CARD_SHARE PlayerNumber FirstSecond TEG.DecryptBroadcast
    | BET_ACTION RoundIndex ActionIndex BettingAction Amount Amount SIG.Signature
    | BETTING_SIGNATURE RoundIndex SIG.Signature
    | COMMUNITY_CARD_OPEN CommunityCardId TEG.DecryptBroadcast
    | CommunityCardOpenedSuccess SIG.Signature
    | SHOW_DOWN ShowDown
    deriving (Show,Eq)

-- ShuffleRows * ShuffleCols ~ NbCards
type ShuffleRows = 4
type ShuffleCols = 13

-- | Player Checking their crytographic material which is:
--
-- * The Player's signature public key
-- * The Player's public broadcast key
-- * The Player's generalised Pedersen commitment parts of ckn
data Checkin ckn = Checkin
    { checkinVerifyKey         :: SIG.VerifyKey
    , checkinPublicBroadcast   :: TEG.PublicBroadcast
    , checkinCommitmentKeyPart :: ListN (ckn+1) Commitment.KeyPart
    }
    deriving (Show,Eq)

-- | Show Down for a player consisting of the decrypt broadcast for first and second cards
data ShowDown = ShowDown
    { showDownFirst  :: TEG.DecryptBroadcast
    , showDownSecond :: TEG.DecryptBroadcast
    } deriving (Show,Eq)

-- | Round index
--
-- 0 is pre flop dealing
-- 1 is after flop dealing
-- 2 is after river dealing
-- 3 is after turn dealing
type RoundIndex = Zn 4

type ActionIndex = Natural
data FirstSecond = First | Second
    deriving (Show,Eq)

-- | Community Card Names
data CommunityCardId = Flop1 | Flop2 | Flop3 | Turn | River
    deriving (Show,Eq,Enum,Bounded)

data BettingAction =
      FOLD
    | CALL
    | RAISE Amount
    | ALLIN
    | CHECK
    deriving (Show,Eq)
