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
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}
module Crypto.Poker
    ( PlayerNumber
    , PlayerIdentity
    , TEG.PublicBroadcast
    , SIG.VerifyKey
    , Result(..)
    , Poker
    , Event(..)
    , runPoker
    , pokerStart
    , GameST(..)
    , initialGameST
    , Operation(..)
    , run
    , generatePrivateInformation
    ) where

import           GHC.TypeLits
import           Control.Monad (when)
import           Data.Proxy
import           Basement.Nat
import           Basement.Bounded
import           Basement.Types.OffsetSize
import           Basement.Compat.Bifunctor
import           Basement.Imports (IsList(..))
import           Foundation.List.ListN (ListN)
import qualified Foundation.List.ListN as ListN
import           Foundation
import           Foundation.Collection

import qualified Crypto.Casino.Primitives.TEG as TEG
import qualified Crypto.Casino.Primitives.SIG as SIG
import qualified Crypto.Casino.Primitives.Permutation as Permutation
import qualified Crypto.Casino.Primitives.Commitment as Commitment
import           Crypto.Casino.ZKSH
import           Crypto.Poker.Card hiding (shuffle)
import           Crypto.Poker.Hand
import           Crypto.Poker.Game
import           Crypto.Poker.Protocol

-- | The chosen 5 community cards unrevealed
data CommunityCardUnrevealed = Unrevealed !EncryptedCard !EncryptedCard !EncryptedCard !EncryptedCard !EncryptedCard

-- | The owner share of the first and second player cards which
-- will be revealed at the showdown
data PlayerOwnShares = PlayerOwnShares TEG.DecryptBroadcast TEG.DecryptBroadcast

-- | Distributed Players encrypted cards
--
-- It has the following order:
--   [P_1 First, P_1 Second, P_2 First, P_2 Second ..., P_n First, P_n Second]
newtype DistributedPlayerCards n = DistributedPlayerCards (ListN (n+n) EncryptedCard)

-- | Known shares for other player card
data OtherPlayerShares = OtherPlayerShares
    { otherCardOwnShare    :: TEG.DecryptSharePoint
    , otherCardOtherShares :: [(PlayerNumber, TEG.DecryptBroadcast)]
    }

-- | Other player cards shares collected for the showdown step
--newtype OtherPlayerShare n = ListN (n-1) TEG.DecryptBroadcast

-- | Get the encrypted cards associated with a player
getPlayerCard :: DistributedPlayerCards n
              -> PlayerNumber             -- ^ The player number which we trying to get the card
              -> FirstSecond              -- ^ The first or second card associated with a player
              -> Poker n EncryptedCard
getPlayerCard (DistributedPlayerCards l) pid ty =
    expectJust ("get player card " <> show pid) $ Just (l `ListN.index` (ofs + t))
  where ofs :: Offset EncryptedCard
        ofs = offsetShiftL 1 (pnToOffset pid)
        t = case ty of
                First  -> 0
                Second -> 1

{-
    playerRound ba player action =
        case action of
            FOLD -> pure $ player { active = False }
            CALL -> do
                unless (ba < r && r <= m && balance player > ba - bet player) compensation
                pure $ player { balance = balance - (r - bet player)
                              , bet     = ba
                              }
            RAISE r -> do
                unless (balance player > r - bet player && ba < r && r <= m) compensation
                pure $ player { balance = balance - (r - bet player)
                              , bet     = r
                              }
            ALLIN -> do
                unless (balance player + bet player <= m) compensation
                pure $ player { balance = 0
                              , bet     = r
                              }
            CHECK ->
                pure player
-}

sendFSC :: SIG.VerifyKey -> TEG.PublicBroadcast -> Poker n ()
sendFSC myVrf myPub = do
    myId <- fsc myVrf myPub
    keyparts <- ListN.replicateM Commitment.keyPartGenerate
    broadcast $ CHECKIN $ Checkin { checkinVerifyKey = myVrf
                                  , checkinPublicBroadcast = myPub
                                  , checkinCommitmentKeyPart = keyparts
                                  }
    setSelfId myId
    pure ()

encryptCard :: TEG.JointPublicKey -> Card -> EncryptedCard
encryptCard jpk c = EncryptedCard $ TEG.encryptionRandom1 jpk (TEG.integerToMessage encryptedIdx)
  where
    -- encrypted index start at 1 whereas card index start at 0
    encryptedIdx :: Integer
    encryptedIdx = 1 + fromIntegral (unZn64 idx)

    idx :: CardIndex
    idx = cardToIndex c

decryptCard :: [(TEG.PublicKey, TEG.DecryptBroadcast)]
            -> EncryptedCard
            -> Maybe Card
decryptCard broadcasts (EncryptedCard ecard) =
    case TEG.verifiableDecrypt broadcasts ecard of
        Nothing           -> Nothing
        Just encryptedIdx ->
            let idx = subtract 1 $ TEG.integerFromMessage encryptedIdx
             in Just $ indexToCard $ zn64 $ fromIntegral idx
  where
    subtract n x = x - n

decryptCardOwn :: TEG.DecryptSharePoint
               -> [(TEG.PublicKey, TEG.DecryptBroadcast)]
               -> EncryptedCard
               -> Maybe Card
decryptCardOwn ownShare others (EncryptedCard ecard) =
    case TEG.verifiableDecryptOwn ownShare others ecard of
        Nothing           -> Nothing
        Just encryptedIdx ->
            let idx = subtract 1 $ TEG.integerFromMessage encryptedIdx
             in Just $ indexToCard $ zn64 $ fromIntegral idx
  where
    subtract n x = x - n

verifyZKSH :: ShuffleProof ShuffleRows ShuffleCols -> Poker n ()
verifyZKSH proof =
    pure ()

-- | Run the poker protocol
--
-- 1) checkin all the players
-- 2) all players iteratively shuffle the decks
-- 3) first 2 players do the small blind and big blind
-- 4) draw initial cards
--    * 2 cards per players
--    * 5 cards for the community
-- 5) main flow where the community cards are revealed (first 3, then fourth, then last)
--    including betting rounds between
-- 6) showdown where player reveal cards and find the winner (if any)
-- 7) pot distribution
run :: forall n . ValidNbPlayers n
    => PrivateInformation
    -> SecurityDeposit
    -> InitialStake
    -> Poker n ()
run privInfo _d _t = do
    players <- step "checkin" (checkin privInfo)
    step "handexecution" (handExecution privInfo players)

checkin :: forall n . ValidNbPlayers n
        => PrivateInformation
        -> Poker n (HandSetup n)
checkin pi = do
    let allCheckins ev =
            case eventGetOperation ev of
                CHECKIN c -> Just c
                _         -> Nothing
    _playerId    <- sendFSC (fst $ privatePublic pi) (snd $ privatePublic pi)
    debug $ show pi
    waitAll @n "CHECKIN" allCheckins $ \l -> do
        let ordered = orderByPlayer l
        vks           <- expectJust "verify keys" $ ListN.toListN $ fmap checkinVerifyKey ordered
        pubs          <- expectJust "public keys" $ ListN.toListN $ fmap (fst . checkinPublicBroadcast) ordered
        jointKey      <- expectJust "joint key" $ TEG.combineVerify $ fmap checkinPublicBroadcast ordered
        commitmentKey <- expectJust "commitment key" $ makeCommitmentKey $ fmap checkinCommitmentKeyPart ordered
        pure $ HandSetup
            { handJointKey      = jointKey
            , handCommitmentKey = commitmentKey
            , handPlayerVKs     = vks
            , handPlayerPubs    = pubs
            }
  where
    orderByPlayer :: [(PlayerNumber, a)] -> [a]
    orderByPlayer = fmap snd . sortBy (compare `on` fst)

    makeCommitmentKey :: [ListN (ShuffleCols+1) Commitment.KeyPart]
                      -> Maybe (Commitment.CommitmentKey ShuffleCols)
    makeCommitmentKey l =
        case sequence $ fmap Commitment.keyPartCombine l of
            Nothing -> Nothing
            Just p  -> Just $ foldl1' Commitment.keyAdd $ nonEmpty_ p

handExecution :: forall n . ValidNbPlayers n
              => PrivateInformation
              -> HandSetup n
              -> Poker n ()
handExecution privateInformation HandSetup {..} = do
    deck <- step "shuffle" shuffle
    step "blinds" blinds
    (playerCards, ecommunityCards) <- step "drawingCards" (drawingCards deck)
    (ownCards, ownShares, otherPlayerCardsShares) <- playerCardOpening playerCards
    communityCards <- step "mainFlow" (mainFlow ownCards ecommunityCards)
    otherPlayerCards <- step "showdown" (showdown playerCards ownShares otherPlayerCardsShares)
    debug (show communityCards <> " || " <> show ownCards <> " || " <> show otherPlayerCards)

    winner <- determineWinner ownCards otherPlayerCards communityCards
    potDistribution winner
  where
    jpk = handJointKey
    ck = handCommitmentKey

    getPlayerKey :: PlayerNumber -> TEG.PublicKey
    getPlayerKey opid = handPlayerPubs `ListN.index` offsetCast Proxy (pnToOffset opid)

    lastPlayerId = natValNatural (Proxy @n)
    lastShuffleRound = natValNatural (Proxy @(n - 1))

    {-
    passAround myTurnToDo someoneElseTurn initial = loop initial 0
      where
        loop passedValue playerRound
            | playerRound == natValNatural (Proxy @n)+1 = pure passedValue
            | otherwise                                 = do
                pid <- getSelfId
                if pid == playerRound
                    then
                        x <- myTurnToDo passedValue
                        broadcast x
                        loop x (playerRound+1)
                    else do
                        x <- wait broadcast of playerRound
                        y <- someoneElseTurn x
                        loop y (playerRound+1)
    -}

    shuffle = do
        let encryptedDeck = ListN.map (encryptCard jpk) newDeck
        shuffleStep 1
        (cards, zksh) <- wait "LAST SHUFFLED" $ \ev -> case eventGetOperation ev of
                                SHUFFLED r cards' zksh' | r == lastShuffleRound -> Just (cards', zksh')
                                _                                               -> Nothing
        verifyZKSH zksh
        pure cards
      where
        shuffleStep playerRound
            | playerRound == natValNatural (Proxy @n)+1 = pure ()
            | otherwise = do
                pid  <- getSelfId
                if | pid == 1 && playerRound == 1 -> shuffleDeck $ ListN.map (encryptCard jpk) newDeck
                   | playerRound == 1             -> pure ()
                   | otherwise                    -> do
                        (_cid, zksh, cards) <- wait ("SHUFFLED " <> show previousPlayer) $ \ev -> case eventGetOperation ev of
                                        SHUFFLED r cards' zksh' | r == previousPlayer -> Just (eventGetPlayerNumber ev, zksh', cards')
                                        _                                             -> Nothing
                        verifyZKSH zksh
                        when (playerRound == pid) $ do
                            shuffleDeck cards
                shuffleStep (playerRound+1)
          where
            previousPlayer = pred playerRound

            shuffleDeck deck = do
                perms        <- Permutation.randomize Permutation.identity
                reEncrypters <- ListN.replicateM @NbCards TEG.randomNew
                let witness = Witness perms reEncrypters
                let unshuffled = UnShuffled $ ListN.map encryptedCardCT deck
                let (Shuffled shuffled) = runShuffle jpk witness unshuffled
                shuffleProof <- shuffleProve jpk ck witness unshuffled
                broadcast (SHUFFLED playerRound (ListN.map EncryptedCard shuffled) shuffleProof)

    eventExpect :: Eq x => Event x -> Event x -> Maybe ()
    eventExpect expected ev
        | expected == ev = Just ()
        | otherwise      = Nothing

    blinds = do
        pid <- getSelfId

        when (pid == 1) $ broadcast SMALLBLIND
        wait "SMALLBLIND" $ eventExpect $ Event 1 SMALLBLIND

        when (pid == 2) $ broadcast BIGBLIND
        wait "BIGBLIND" $ eventExpect $ Event 2 BIGBLIND
        -- TODO adjust balance & bet

    drawingCards :: ListN NbCards EncryptedCard -> Poker n (DistributedPlayerCards n, CommunityCardUnrevealed)
    drawingCards cards = do
        -- here we use a different order than the traditional game, but
        -- considering we're dealing with an encrypted deck of multi party shuffled card
        -- with idealistic shuffle probability, it doesn't really matter the order in which we get cards
        -- as long as each party used the same convention.

        let distributed = ListN.take cards :: ListN (n+n) EncryptedCard
            communityCardsList = take 5 $ drop (natValCountOf (Proxy @(n+n))) (ListN.unListN cards)

        communityCards <- case communityCardsList of
                                [c1,c2,c3,c4,c5] -> pure $ Unrevealed c1 c2 c3 c4 c5
                                _                -> failed "community cards internal error"
        pure (DistributedPlayerCards distributed, communityCards)

    getDrawCardOpeningFor ty pid ev =
         case eventGetOperation ev of
                DRAW_CARD_SHARE rpid rty db | rpid == pid && rty == ty -> Just db
                _                                                      -> Nothing

    getShowdown ev =
        case eventGetOperation ev of
            SHOW_DOWN s -> Just s
            _           -> Nothing

    -- here we broadcast all the shares that need to be,
    -- then try to open our own card with the shares
    playerCardOpening :: DistributedPlayerCards n
                      -> Poker n (PlayerCards, PlayerOwnShares, [((PlayerNumber, FirstSecond), OtherPlayerShares)])
    playerCardOpening distributed = do
        selfid <- getSelfId

        otherPlayers <- allPlayerNumbersExceptMe

        -- broadcast shares for all player cards except ours
        forM_ otherPlayers $ \pid ->
            forM_ [First,Second] $ \ty -> do
                (EncryptedCard ecard) <- getPlayerCard distributed pid ty
                db <- TEG.decryptShare (privateSecret privateInformation) ecard
                broadcast $ DRAW_CARD_SHARE pid ty db

        let grabCardSharesAndDecrypt ty =
                waitAllButMe @n ("DRAW_CARD_SHARE " <> show ty) (getDrawCardOpeningFor ty selfid) $ \l -> do
                    ecard@(EncryptedCard ecard') <- getPlayerCard distributed selfid ty

                    ownShare <- TEG.decryptShare (privateSecret privateInformation) ecard'

                    let decryptBroadcast = fmap (first getPlayerKey) l

                    c <- expectJust ("card " <> show selfid <> " " <> show ty) $ decryptCardOwn (fst ownShare) decryptBroadcast ecard
                    pure (c, ownShare)

        -- recover all shares for all other players, for the showdown step
        otherShares <-
            forM otherPlayers $ \pid ->
                forM [First,Second] $ \ty ->
                    waitAllBut @n ("OTHER SHARE " <> show pid <> " " <> show ty)
                                  (\x -> if x == selfid || x == pid then NoWait else Wait)
                                  (getDrawCardOpeningFor ty pid) $ \l -> do
                        ecard@(EncryptedCard ecard') <- getPlayerCard distributed pid ty
                        -- this is duplicated from above..
                        ownShare <- TEG.decryptShare (privateSecret privateInformation) ecard'

                        pure ((pid, ty), OtherPlayerShares (fst ownShare) l)

        (c1,s1) <- grabCardSharesAndDecrypt First
        (c2,s2) <- grabCardSharesAndDecrypt Second

        debug ("player cards " <> show c1 <> " and " <> show c2)

        pure (PlayerCards c1 c2, PlayerOwnShares s1 s2, mconcat otherShares)

    mainFlow ownCards (Unrevealed eflop1 eflop2 eflop3 eturn eriver) = do
        bettingRound (privateSigning privateInformation) (zn 0) 3
        flop1 <- communityCardOpen Flop1 eflop1
        flop2 <- communityCardOpen Flop2 eflop2
        flop3 <- communityCardOpen Flop3 eflop3
        bettingRound (privateSigning privateInformation) (zn 1) 1
        turn <- communityCardOpen Turn eturn
        bettingRound (privateSigning privateInformation) (zn 2) 1
        river <- communityCardOpen River eriver
        bettingRound (privateSigning privateInformation) (zn 3) 1
        pure $ CommunityCards flop1 flop2 flop3 turn river

    showdown :: DistributedPlayerCards n
             -> PlayerOwnShares
             -> [((PlayerNumber, FirstSecond), OtherPlayerShares)]
             -> Poker n [(PlayerNumber, PlayerCards)]
    showdown playerCards (PlayerOwnShares s1 s2) otherPlayerCards = do
        -- broadcast the owner shares
        broadcast (SHOW_DOWN $ ShowDown s1 s2)

        -- get all other broadcasts and decrypt
        otherShowdowns <- waitAllButMe @n "SHOWDOWN" getShowdown pure
        otherPlayers <- allPlayerNumbersExceptMe

        let decryptOtherCard player ty = do
                ecard@(EncryptedCard ecard') <- getPlayerCard playerCards player ty
                otherCard <- expectJust "other card" $ lookup (player, ty) otherPlayerCards
                let ownShare  = otherCardOwnShare otherCard
                    pubShares = fmap (first getPlayerKey) $ otherCardOtherShares otherCard
                pshowdown <- expectJust "xyz" $ lookup player otherShowdowns
                let k = getPlayerKey player
                let sshare = case ty of
                                First  -> showDownFirst pshowdown
                                Second -> showDownSecond pshowdown
                expectJust "other card 2" $ decryptCardOwn ownShare (pubShares <> [(k,sshare)]) ecard

        -- get all the other players cards
        forM otherPlayers $ \pid -> do
            c1 <- decryptOtherCard pid First
            c2 <- decryptOtherCard pid Second
            pure (pid, PlayerCards c1 c2)

    potDistribution _winner = -- TODO
        pure ()
    communityCardOpen ty ecard@(EncryptedCard cc) = do
        -- (EncryptedCard cc) <- getEncryptedCommunityCard ty
        di <- TEG.decryptShare (privateSecret privateInformation) cc
        broadcast (COMMUNITY_CARD_OPEN ty di)

        let allCommunityCardOpening ev =
                case eventGetOperation ev of
                    COMMUNITY_CARD_OPEN rty di | rty == ty -> Just di
                    _                                      -> Nothing

        openedCard <- waitAll @n "COMMUNITY CARD OPEN" allCommunityCardOpening $ \l -> do
            let decryptBroadcast = fmap (first getPlayerKey) l
            expectJust "card" $ decryptCard decryptBroadcast ecard

        -- broadcast (CommunityCardOpened openedSig)

        -- sigs <- waitAll @n "SOMETHING" undefined $ undefined
        -- pure openedCard
        debug ("card opened " <> show ty <> " " <> show openedCard)
        pure openedCard

-- | Betting round
bettingRound :: forall n . ValidNbPlayers n
             => SIG.SigningKey
             -> RoundIndex
             -> PlayerNumber
             -> Poker n ()
bettingRound sigKey roundId initialPlayer = do
    updatedBetStatus <- betRound 0 initialPlayer (ListN.replicate initialPlayerCurrentBet)
    betSign updatedBetStatus
  where

    sigmsgBalanceBets betStatus = do
        -- TODO: generate a signature message for all bets and all balances
        pure $ placeholderMessage

    betSign betStatus = do
        msg    <- sigmsgBalanceBets betStatus
        mySig  <- withRng $ SIG.sign sigKey msg
        broadcast (BETTING_SIGNATURE roundId mySig)

        otherSigs <- waitAllButMe @n "BETTING SIGNATURE" (\ev ->
            case eventGetOperation ev of
                BETTING_SIGNATURE rid sig | rid == roundId -> Just sig
                _                                          -> Nothing) pure

        forM_ otherSigs $ \(opid, sig) -> do
            -- verify all signatures
            pure ()

    betRound :: Natural -> PlayerNumber -> ListN n PlayerCurrentBet -> Poker n (ListN n PlayerCurrentBet)
    betRound actIdx currentPlayer bettingStatus = do
        let finished = isBetRoundFinish bettingStatus
        if finished
            then pure bettingStatus
            else do
                {-
                status <- active <$> getPlayer @n currentPlayer
                (newIdx, ret) <- case status of
                            Folded    -> pure actIdx
                            IsAllIn   -> pure actIdx
                            Betting   -> doBetting
                            NotBetYet -> doBetting
                            -}
                (newIdx, ret) <- doBetting
                next <- nextPlayer currentPlayer
                betRound newIdx next ret
      where
        doBetting = do
            currentPlayer <- isCurrentPlayer currentPlayer
            if currentPlayer
                then do
                    --act <- userBet
                    act <- pure $ CALL
                    sig <- withRng $ SIG.sign sigKey placeholderMessage
                    broadcast (BET_ACTION roundId actIdx act 0 0 sig)
                    processBet act
                else do
                    -- wait previous player action
                    prevAction <- wait "BET ACTION" $ \ev -> case eventGetOperation ev of
                                            BET_ACTION pRid pIdx bAct _ _ _
                                                | pRid == roundId && pIdx == actIdx -> Just bAct
                                            _ -> Nothing
                    processBet prevAction
        processBet action = do
            let l = ListN.updateAt (pnToOffset currentPlayer) (\pb -> pb { status = Betting }) bettingStatus
            pure (actIdx+1, l)

    isBetRoundFinish st =
        -- TODO for now we just make sure everyone betted once
        all ((/= NotBetYet) . status) (ListN.unListN st)

nextPlayer :: forall n . ValidNbPlayers n => PlayerNumber -> Poker n PlayerNumber
nextPlayer pid = do
    ps <- allPlayerNumbers (Proxy @n)
    pure $ case dropWhile (/= pid) ps of
        []      -> error "invalid nextPlayer"
        [_]     -> head $ nonEmpty_ ps
        (_:x:_) -> x

data WinStatus = Won | Lost PlayerNumber
    deriving (Show,Eq)

determineWinner
    :: forall n . ValidNbPlayers n
    => PlayerCards
    -> [(PlayerNumber, PlayerCards)]
    -> CommunityCards
    -> Poker n PlayerNumber
determineWinner myOwnCards otherPlayerCards (CommunityCards c1 c2 c3 c4 c5) = do
    let otherResult = nonEmpty_ $ reverse $ sortBy (compare `on` snd) $ fmap (second (handFindHighest . combineHand)) otherPlayerCards
        myResult = handFindHighest $ combineHand myOwnCards
    if myResult > snd (head otherResult)
        then do
            debug ("WON " <> show myResult <> " " <> show otherResult)
            pure 0
        else do
            let (winner, r) = head otherResult
            debug ("LOST " <> show winner <> " " <> show r <> " MINE IS " <> show myResult)
            pure winner
  where
    communityHand = toHand [c1,c2,c3,c4,c5]
    combineHand (PlayerCards p1 p2) = toHand [p1,p2] `merge` communityHand

placeholderMessage :: UArray Word8
placeholderMessage = fromList [1]
