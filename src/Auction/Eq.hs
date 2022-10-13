{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | This module proves that Eq instances of ADTs in the
-- Auction contract [1] are defined correctly.
--
-- [1] https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs
module Auction.Eq where

-- Omitting this flag causes crashes when digesting imported
-- definitions
{-@ LIQUID "--exact-data-cons" @-}

import qualified Data.ByteString
import qualified Plutus as Pl
import Prelude hiding (Eq(..))
import qualified Prelude (Eq(..))

-- Adding a specification to a type class requires all the
-- instances to respect the specification.
--
-- For the case of @Eq@, we require the meaning of (==) to match
-- the meaning of @=@ in the SMT solver.
{-@
class Eq a where
  (==) :: x:a -> y:a -> { v:Bool | v = (x = y) }
@-}
class Eq a where
  (==) :: a -> a -> Bool

data BidderInfo = BidderInfo
  { -- | the last bidder's offer in Ada
    bid :: Integer,
    -- | the last bidder's address
    bidder :: Pl.PubKeyHash
  }

instance Eq BidderInfo where
  BidderInfo a b == BidderInfo x y = (Prelude.==) a x && (Prelude.==) b y

-- | The state of the auction. This will be the 'DatumType'.
data AuctionState
  = -- | state of an auction that has not yet had any bids
    NoBids
  | -- | state of an auction that has had at least one bid
    Bidding BidderInfo

instance Eq AuctionState where
  NoBids == NoBids = True
  Bidding a == Bidding x = a == x
  _ == _ = False

-- | Actions to be taken in an auction. This will be the 'RedeemerType'.
data Action
  = -- | redeemer to make a bid (before the 'bidDeadline')
    Bid BidderInfo
  | -- | redeemer to close the auction (after the 'bidDeadline')
    Hammer

instance Eq Action where
  Bid bi1 == Bid bi2 = bi1 == bi2
  Hammer == Hammer = True
  _ == _ = False

--------------------------------------------------
-- Limitations
--------------------------------------------------
--
-- The following limitations have been found
--
-- * We can attach a specification to 'PlutusTx.Eq.Eq', and then demand that
--   every instance of @Eq@ in a module that enables LH is verified. However,
--   we will have to see how to attach this specification, as doing this from
--   a different module to that in which the class is defined produces unclear
--   errors.
