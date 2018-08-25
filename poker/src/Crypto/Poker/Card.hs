{-# LANGUAGE GADTs         #-}
{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Crypto.Poker.Card where

import           GHC.TypeLits
import           GHC.Generics
import           Control.DeepSeq
import           Basement.Nat
import           Basement.Bounded
import           Foundation.List.ListN (ListN)
import qualified Foundation.List.ListN as ListN
import           Foundation
import           Data.Function (on)
import qualified Prelude

-- | Card Suits
data Suit = Clubs | Diamonds | Hearts | Spades
    deriving (Show,Eq,Ord,Enum,Bounded,Generic)

-- | Card Ranks
data Rank = R2 | R3 | R4 | R5 | R6 | R7 | R8 | R9 | R10 | Jack | Queen | King | Ace
    deriving (Show,Eq,Ord,Enum,Bounded,Generic)

suitPretty :: Suit -> Char
suitPretty Clubs = '♣'
suitPretty Diamonds = '♦'
suitPretty Hearts = '♥'
suitPretty Spades = '♠'

instance NFData Suit
instance NFData Rank

type CardIndex = Zn64 NbCards

allCardIndices :: [CardIndex]
allCardIndices = fmap zn64 [0..51]

data Card = Card { cardSuit :: Suit, cardRank :: Rank }
    deriving (Eq,Generic)

instance Show Card where
    show (Card s r) =
        suitPretty s : Prelude.show r

instance NFData Card

type NbCards = 52
type PlayersCards = 47 -- 52 - 5 community cards
type MaxPlayers = 23 -- 2 cards per players

type Deck n card = ListN n card

type ComboRank = Zn 9

data CommunityCards = CommunityCards Card Card Card Card Card
    deriving (Show,Eq)
data PlayerCards = PlayerCards Card Card
    deriving (Show,Eq)

data HighestCombo =
      CardHigh Card
    | Pair Rank
    | TwoPairs Card Card Card
    | ThreeKind Rank
    | Straight Rank -- e.g. 5, 6, 7, 8, 9 = Straight 9
    | Flush Suit Rank -- highest card
    | FullHouse Rank Rank -- e.g. 5,5,5,7,7 = FullHouse 5 7
    | FourKind Rank
    | StraightFlush Suit Rank -- e.g. Hearts 3,4,5,6,7 = StraighFlush Heart 7
    | RoyalFlush Suit -- 10, J, Q, K, A - 1 color
    deriving (Show, Eq)

data ComboType =
      ComboHighCard
    | ComboPair
    | ComboTwoPairs
    | ComboThreeKinds
    | ComboStraight
    | ComboFlush
    | ComboFullHouse
    | ComboFourKinds
    | ComboStraightFlush
    | ComboRoyalFlush
    deriving (Show,Eq,Ord)

comboNbCards :: HighestCombo -> Word
comboNbCards (RoyalFlush {}) = 5
comboNbCards (StraightFlush {}) = 5
comboNbCards (FourKind {}) = 4
comboNbCards (FullHouse {}) = 5
comboNbCards (Flush {}) = 5
comboNbCards (Straight {}) = 5
comboNbCards (ThreeKind {}) = 3
comboNbCards (TwoPairs {}) = 4
comboNbCards (Pair {}) = 2
comboNbCards (CardHigh {}) = 1

cardToIndex :: Card -> CardIndex
cardToIndex (Card suit rank) = zn64 $ fromIntegral (13 * fromEnum suit + fromEnum rank)

indexToCard :: CardIndex -> Card
indexToCard (unZn64 -> n) = Card (toEnum suit) (toEnum rank)
  where
    (suit, rank) = fromIntegral n `divMod` 13

-- | Create a new Deck of all the card
newDeck :: Deck NbCards Card
newDeck = ListN.toListN_
    [ Card suit rank
    | suit <- [minBound..maxBound]
    , rank <- [minBound..maxBound]
    ]

maximumByRank :: [Card] -> Card
maximumByRank []     = error "cannot be used on empty"
maximumByRank (h:hs) = loop h hs
  where loop m [] = m
        loop m (x:xs)
            | cardRank x > cardRank m = loop x xs
            | otherwise               = loop m xs

instance Ord HighestCombo where
    compare c1 c2 =
        case rankCombo c1 `compare` rankCombo c2 of
            LT -> LT
            GT -> GT
            EQ -> case (c1, c2) of
                    (RoyalFlush _       , RoyalFlush _       ) -> EQ
                    (StraightFlush _ r1 , StraightFlush _ r2 ) -> compare r1 r2
                    (FourKind r1        , FourKind r2        ) -> compare r1 r2
                    (FullHouse r1 p1    , FullHouse r2 p2    ) -> compare r1 r2 `mappend` compare p1 p2
                    (Flush _ _          , Flush _ _          ) -> error "flush comparaison not implementeD"
                    (Straight _         , Straight _         ) -> error "straight compar not implemented"
                    (ThreeKind _        , ThreeKind _        ) -> error "three kind not implemented"
                    (TwoPairs a1 b1 l1  , TwoPairs a2 b2 l2  ) -> compareRank a1 a2 `mappend` compareRank b1 b2 `mappend` compareRank l1 l2
                    (Pair _             , Pair _             ) -> error "pair not implemneted"
                    (CardHigh _         , CardHigh _         ) -> error "card high not implemented"
                    (_                  , _                  ) -> error "compare highest combo"

rankCombo :: HighestCombo -> ComboRank
rankCombo (CardHigh _)        = zn 0
rankCombo (Pair _)            = zn 1
rankCombo (TwoPairs _ _ _)    = zn 2
rankCombo (ThreeKind _)       = zn 3
rankCombo (Straight _)        = zn 4
rankCombo (Flush _ _)         = zn 5
rankCombo (FullHouse _ _)     = zn 6
rankCombo (FourKind _)        = zn 7
rankCombo (StraightFlush _ _) = zn 8
rankCombo (RoyalFlush _)      = zn 9

compareRank :: Card -> Card -> Ordering
compareRank = compare `on` cardRank

shuffle :: forall n card . (NatWithinBound Int n, KnownNat n)
        => Word
        -> [Zn n]
        -> ListN n card
        -> ListN n card
shuffle nbRepeat sched = maybe (error "internal error") id
                       . ListN.toListN
                       . loop nbRepeat sched
                       . ListN.unListN
  where
    --len = natVal (Proxy :: Proxy n)

    loop :: Word -> [Zn n] -> [card] -> [card]
    loop n []               l          = loop n sched l
    loop _ _                []         = []
    loop _ _                l@(_:_:[]) = l
    loop 0 _                l          = l
    loop n ((unZn -> s):ss) l          =
        let (a,b) = splitAt (fromIntegral s) l
            r     = loop (n-1) ss b <> loop (n-1) ss a
         in loop (n-1) ss r
