{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Crypto.Poker.Hand
    ( Hand
    , toHand
    , fromHand
    , add
    , remove
    , removeHand
    , merge
    , mergeSuits
    , elem
    , subsetOf
    , maximumRank
    , highestCard
    , onlyRank
    , removeRank
    , onlySuit
    , cardsIn
    , handFindHighest
    ) where

import           Basement.Imports
import           Basement.Numerical.Additive
import           Basement.Numerical.Multiplicative
import           Data.Bits (setBit, clearBit, testBit, (.&.), (.|.), popCount, complement, shiftL, shiftR)
import           Data.List (foldl', find, maximum, reverse, lookup, sortBy)
import           Data.Function (on)
import qualified Prelude
import           Crypto.Poker.Card
import           Control.Monad
import           Text.Printf (printf)

newtype Hand = Hand Word64
    deriving (Eq)

instance Ord Hand where
    compare = compare `on` handFindHighest

instance Show Hand where
    show (Hand w) = printf "%016x" w

data CardAlreadySet = CardAlreadySet Card
    deriving (Show,Eq,Typeable)

instance Exception CardAlreadySet

type CardOffset = Int -- should be Zn64 for clean type, but Data.Bits and Enum are both Int based

-- 3 bits per suits are skipped so that we can align to a boundary
cardToOfs :: Card -> CardOffset
cardToOfs (Card suit rank) = (16 * fromEnum suit + fromEnum rank)

ofsToCard :: CardOffset -> Card
ofsToCard n = Card (toEnum suit) (toEnum rank)
  where
    (suit, rank) = Prelude.fromIntegral n `divMod` 16

-- | Set a card
setCard :: CardOffset -> Hand -> Hand
setCard !co !(Hand bitmap) = Hand (bitmap `setBit` co)

clearCard :: CardOffset -> Hand -> Hand
clearCard !co !(Hand bitmap) = Hand (bitmap `clearBit` co)

cardsIn :: Hand -> Word
cardsIn (Hand w) = Prelude.fromIntegral (popCount w)

fromHand :: Hand -> [Card]
fromHand (Hand w) = loop 0
  where loop i
            | i == 64           = []
            | (i `mod` 16) > 12 = loop (i+1)
            | w `testBit` i     = ofsToCard i : loop (i+1)
            | otherwise         = loop (i+1)

toHand :: [Card] -> Hand
toHand = foldl' f emptyHand
  where f !acc c = setCard (cardToOfs c) acc

emptyHand :: Hand
emptyHand = Hand 0

merge :: Hand -> Hand -> Hand
merge (Hand a) (Hand b) = Hand (a .|. b)


add :: Card -> Hand -> Hand
add = setCard . cardToOfs

remove :: Card -> Hand -> Hand
remove = clearCard . cardToOfs

elem :: Card -> Hand -> Bool
elem c (Hand w) = w `testBit` cardToOfs c

-- | Try to find a rank @r@ in a hand, and if found return the Suit
--
-- > lookupRank R8 (toHand [R8])
lookupRank :: Rank -> Hand -> Maybe Suit
lookupRank r h = lookup True $ fmap (\s -> (elem (Card s r) h, s)) [minBound..maxBound]

-- | Check if the first parameter Hand is contained in the second parameter Hand
subsetOf :: Hand -- subset to test for
         -> Hand -- the hand of card to test for
         -> Bool
subsetOf (Hand needles) (Hand haystack) =
    (needles .&. haystack) == needles

-- | Remove a hand from another hand
removeHand :: Hand -- hand to remove from the input hand
           -> Hand -- input hand
           -> Hand -- output hand which is input minus all the card to remove
removeHand (Hand w) (Hand h) = Hand (complement w .&. h)

-- | Filter a hand by keeping only the cards of Suit @suit@
onlySuit :: Suit -> Hand -> Hand
onlySuit suit (Hand w) =
    Hand (w .&. (0xffff `shiftL` (mask * 16)))
  where mask = fromEnum suit

-- | Filter a hand by keeping only the cards of Rank @rank@
onlyRank :: Rank -> Hand -> Hand
onlyRank rank (Hand w) =
    Hand (w .&. mask)
  where mask1 = 0 `setBit` fromEnum rank
        mask2 = mask1 .|. (mask1 `shiftL` 16)
        mask  = mask2 .|. (mask2 `shiftL` 32)

-- | Filter a hand by keeping only the cards that are of Rank @rank@
removeRank :: Rank -> Hand -> Hand
removeRank rank (Hand w) =
    Hand (w .&. complement mask)
  where mask1 = 0 `setBit` fromEnum rank
        mask2 = mask1 .|. (mask1 `shiftL` 16)
        mask  = mask2 .|. (mask2 `shiftL` 32)

-- | Get the card for a specific rank if existing
--
-- The suit order of which is it done is arbitrary
getByRank :: Rank -> Hand -> Maybe Card
getByRank r h = flip Card r <$> lookupRank r h

-- | merge all the suits to the Club suits
--
-- each rank are represented by Clubs as result
mergeSuits :: Hand -> Hand
mergeSuits (Hand w) = Hand $
    ( w              .&. 0xffff) .|.
    ((w `shiftR` 16) .&. 0xffff) .|.
    ((w `shiftR` 32) .&. 0xffff) .|.
    ((w `shiftR` 48) .&. 0xffff)

-- cardToOfs (Card suit rank) = (16 * fromEnum suit + fromEnum rank)

maximumRank :: Hand -> Rank
maximumRank h
    | h == emptyHand = error "cannot get rank on empty hand"
    | otherwise      = maximum $ fmap cardRank $ fromHand h

highestCard :: Hand -> Maybe Card
highestCard h
    | h == emptyHand = Nothing
    | otherwise      = Just $ maximumByRank $ fromHand h

data HighestResult = HighestResult
    { highestCombo     :: ComboType
    , highestComboHand :: Hand
    , highestRemaining :: Hand
    } deriving (Eq)

instance Show HighestResult where
    show (HighestResult combo hand remaining) =
        Prelude.show combo <> " " <> Prelude.show (fromHand hand) <> " + " <> Prelude.show (fromHand remaining)

instance Ord HighestResult where
    compare (HighestResult combo1 chand1 rem1) (HighestResult combo2 chand2 rem2) =
        compare combo1 combo2 <> comboCompare combo1 chand1 chand2 <> (maximumRank rem1 `compare` maximumRank rem2)
      where
        comboCompare ComboHighCard h1 h2 = maximumRank h1 `compare` maximumRank h2
        comboCompare ComboPair h1 h2 = maximumRank h1 `compare` maximumRank h2
        comboCompare ComboTwoPairs h1 h2 = compareHandRanks h1 h2
        comboCompare ComboThreeKinds h1 h2 = maximumRank h1 `compare` maximumRank h2
        comboCompare ComboStraight h1 h2 = maximumRank h1 `compare` maximumRank h2
        comboCompare ComboFlush h1 h2 = compareHandRanks h1 h2
        comboCompare ComboFullHouse h1 h2 = compareHandRanks h1 h2
        comboCompare ComboFourKinds h1 h2 = maximumRank h1 `compare` maximumRank h2
        comboCompare ComboStraightFlush h1 h2 = compareHandRanks h1 h2
        comboCompare ComboRoyalFlush _ _ = error "impossible"

-- | Only call with the same number of cards
compareHandRanks :: Hand -> Hand -> Ordering
compareHandRanks h1 h2
    | h1 == emptyHand && h2 == emptyHand = EQ
    | cardsIn h1 /= cardsIn h2           = error "not same number of cards"
    | otherwise                          = (r1 `compare` maximumRank h2) <> compareHandRanks (removeRank r1 h1) (removeRank r1 h2)
  where r1 = maximumRank h1

-- | Return the highest combo type with the associated hand and the leftover hands
handFindHighest :: Hand -> Maybe HighestResult
handFindHighest hand = testCombi hand
    [ (ComboRoyalFlush, royalFlush)
    , (ComboStraightFlush, straightFlush)
    , (ComboFourKinds, fourKind)
    , (ComboFullHouse, fullHouse)
    , (ComboStraight, straight)
    , (ComboFlush, flush)
    , (ComboThreeKinds, threeKind)
    , (ComboTwoPairs, twoPairs)
    , (ComboPair, pair)
    , (ComboHighCard, highCard)
    ]
  where
    testCombi _ [] = Nothing
    testCombi h ((c, x):xs)
        | cardsIn h == 0 = Nothing
        | otherwise      =
            case x h of
                Nothing        -> testCombi h xs
                Just foundHand -> Just $ HighestResult { highestCombo     = c
                                                       , highestComboHand = foundHand
                                                       , highestRemaining = removeHand foundHand h
                                                       }

    royalFlush h = findHand 5 allHands h
      where allHands = applySuits allSuits [Ace,King,Queen,Jack,R10]

    straightFlush h = findHand 5 allHands h
      where allHands = mconcat $ fmap (applySuits allSuits) straightFlushRanks
            straightFlushRanks =
                [ let b = pred a; c = pred b; d = pred c; e = pred d in [a,b,c,d,e]
                | a <- [King,Queen,Jack,R10,R9,R8,R7,R6]
                ]
    straight h = loopTry allStarts $ \a ->
                    let b = pred a; c = pred b; d = pred c; e = pred d
                     in toHand <$> (mapM (\r -> getByRank r h) [a,b,c,d,e])
      where allStarts = [King,Queen,Jack,R10,R9,R8,R7,R6]

    -- there can't be 2 flush in one player's hand, so it's ok to take the first one.
    flush h = loopTry (fmap checkSuit allSuits) id
      where checkSuit s
                | cardsIn sh >= 5 = Just (toHand $ Prelude.take 5 $ sortBy compareRank $ fromHand sh)
                | otherwise       = Nothing
              where sh = onlySuit s h

    fourKind h = findWithRanks 4 (\_ found -> if cardsIn found == 4 then Just found else Nothing) h
    threeKind h = findWithRanks 3 (\_ found -> if cardsIn found == 3 then Just found else Nothing) h
    pair h = findWithRanks 2 (\_ found -> if cardsIn found == 2 then Just found else Nothing) h
    highCard h = toHand . (:[]) <$> highestCard h

    twoPairs = pair `followedBy` pair
    fullHouse = threeKind `followedBy` pair

    -- - - - - - - - - - -
    -- combinators and helpers
    -- - - - - - - - - - -

    followedBy a b h =
        case a h of
            Just found -> case b (removeHand found h) of
                                Nothing     -> Nothing
                                Just found2 -> Just (found `merge` found2)
            Nothing    -> Nothing

    allSuits = [minBound..maxBound]
    allRanks = [minBound..maxBound]

    applySuit suit l = toHand $ fmap (Card suit) l

    applySuits suits l = fmap (flip applySuit l) suits

    -- try to find a match against specific hands
    -- the hand need to in decreasing order of ranking
    findHand :: Word
             -> [Hand]
             -> Hand
             -> Maybe Hand
    findHand atLeast hands toSearch
        | cardsIn toSearch >= atLeast = find (flip subsetOf toSearch) hands
        | otherwise                   = Nothing

    findWithRanks :: Word
                  -> (Rank -> Hand -> Maybe Hand)
                  -> Hand
                  -> Maybe Hand
    findWithRanks atLeast finder toSearch
        | cardsIn toSearch >= atLeast = loopTry (reverse allRanks) $ \r -> finder r (onlyRank r toSearch)
        | otherwise                   = Nothing

    loopTry :: [x] -> (x -> Maybe a) -> Maybe a
    loopTry []     _ = Nothing
    loopTry (x:xs) f = f x `mplus` loopTry xs f
