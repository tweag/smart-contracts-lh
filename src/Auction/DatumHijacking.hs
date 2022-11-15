{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | This module proves with Liquid Haskell that the Auction
-- contract in [1] doesn't have the datum hijacking bug [2].
--
-- [1] https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs
-- [2] https://github.com/tweag/audit-docs/blob/master/VULNERABILITIES.md#cv001-datum-hijacking
module Auction.DatumHijacking where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-cons" @-}

import qualified Data.ByteString -- needed to avoid LH crash
import qualified Plutus as Pl

-- | All the statically known data associated with an auction that the
-- validator needs to know
data StaticValParams = StaticValParams
  { -- | no bids are accepted later than this
    bidDeadline' :: Pl.POSIXTime,
    -- | minimum bid in Lovelace
    minBid' :: Integer,
    -- | value that is being auctioned
    lot' :: Pl.Value
  }

data ValParams = ValParams
  { staticValParams :: StaticValParams,
    -- | address of the seller
    seller :: Pl.PubKeyHash,
    threadTokenAssetClass :: Pl.AssetClass
  }

-- | The state of the auction. This will be the 'DatumType'.
data AuctionState
  = -- | state of an auction that has not yet had any bids
    NoBids
  | -- | state of an auction that has had at least one bid
    Bidding BidderInfo
  deriving Eq

data BidderInfo = BidderInfo
  { -- | the last bidder's offer in Ada
    bid :: Integer,
    -- | the last bidder's address
    bidder :: Pl.PubKeyHash
  }
  deriving Eq

-- TODO: check that the value in the output is the expected one

{-@ reflect hasOnlyOneContinuingOutputWithDatum @-}
hasOnlyOneContinuingOutputWithDatum :: Pl.ScriptContext -> AuctionState -> Bool
hasOnlyOneContinuingOutputWithDatum ctx datum =
     case getContinuingOutputs ctx of
       [o] ->
           outputAuctionState (Pl.scriptContextTxInfo ctx) o
             == Just datum
       _ -> False

{-@
measure Auction.DatumHijacking.getContinuingOutputs :: Pl.ScriptContext -> [Pl.TxOut]
assume getContinuingOutputs
  :: x:Pl.ScriptContext -> {v:[Pl.TxOut] | Auction.DatumHijacking.getContinuingOutputs x = v }
@-}
getContinuingOutputs :: Pl.ScriptContext -> [Pl.TxOut]
getContinuingOutputs = undefined

{-@
measure Auction.DatumHijacking.outputAuctionState :: Pl.TxInfo -> Pl.TxOut -> Maybe AuctionState
assume outputAuctionState
  :: x:Pl.TxInfo -> y:Pl.TxOut -> { v:Maybe AuctionState | Auction.DatumHijacking.outputAuctionState x y = v }
@-}
outputAuctionState :: Pl.TxInfo -> Pl.TxOut -> Maybe AuctionState
outputAuctionState = undefined

bidTimeRange :: ValParams -> Pl.POSIXTimeRange
bidTimeRange a = Pl.to (bidDeadline a)

bidDeadline :: ValParams -> Pl.POSIXTime
bidDeadline = bidDeadline' . staticValParams

minBid :: ValParams -> Integer
minBid = minBid' . staticValParams

lot :: ValParams -> Pl.Value
lot = lot' . staticValParams

-- | Test that the value paid to the giv,en public key address is at
-- least the given value
receivesFrom :: Pl.TxInfo -> Pl.PubKeyHash -> Pl.Value -> Bool
receivesFrom txi who what = Pl.valuePaidTo txi who `Pl.geq` what

{-@
validBid
  :: auction:ValParams
  -> datum:AuctionState
  -> bid:Integer
  -> bidder:Pl.PubKeyHash
  -> ctx:Pl.ScriptContext
  -> { v:Bool
     | v => hasOnlyOneContinuingOutputWithDatum ctx (Bidding (BidderInfo bid bidder))
     }
@-}

-- | A new bid is valid if
-- * it is made before the bidding deadline
-- * it has been signed by the bidder
-- * it is greater than maximum of the lastBid and the minBid
-- * after the transaction:
--    * the state of the auction is 'Bidding' with the new bid and bidder
--    * the validator locks the lot, the new bid, and the thread token
--    * the last bidder has gotten their money back from the validator
validBid :: ValParams -> AuctionState -> Integer -> Pl.PubKeyHash -> Pl.ScriptContext -> Bool
validBid auction datum bid bidder ctx =
  let txi = Pl.scriptContextTxInfo ctx
      selfh = Pl.ownHash ctx
      receives = receivesFrom txi
   in
      Pl.traceIfFalse
        "Bidding past the deadline is not permitted"
        (bidTimeRange auction `Pl.contains` Pl.txInfoValidRange txi)
      &&
        Pl.traceIfFalse "Bid transaction not signed by bidder" (txi `Pl.txSignedBy` bidder)
      && Pl.traceIfFalse
          "Validator does not lock lot, bid, and thread token"
          ( Pl.valueLockedBy txi selfh
              `Pl.geq` ( lot auction <> Pl.lovelaceValueOf bid
                           <> Pl.assetClassValue (threadTokenAssetClass auction) 1
                       )
          )
      &&
        checkOutput ctx bid bidder
      && case datum of
          NoBids ->
            Pl.traceIfFalse "Cannot bid less than the minimum bid" (minBid auction <= bid)
          Bidding (BidderInfo lastBid lastBidder) ->
            Pl.traceIfFalse "Must bid more than the last bid" (lastBid < bid)
              && Pl.traceIfFalse
                "Last bidder is not paid back"
                (lastBidder `receives` Pl.lovelaceValueOf lastBid)

-- Apparently, we need to tell LH the refinement type to infer for the code
-- that checks datum hijacking, otherwise, LH can't verify validBid.
--
-- Initially, checkOutput was inlined at the call site.

{-@
checkOutput
  :: ctx:Pl.ScriptContext
  -> bid:Integer
  -> bidder:Pl.PubKeyHash
  -> { v:Bool
     | v => hasOnlyOneContinuingOutputWithDatum ctx (Bidding (BidderInfo bid bidder))
     }
@-}
checkOutput :: Pl.ScriptContext -> Integer -> Pl.PubKeyHash -> Bool
checkOutput ctx bid bidder =
  let txi = Pl.scriptContextTxInfo ctx
   in case getContinuingOutputs ctx of {
          [o] ->
            Pl.traceIfFalse
              "Not in the correct 'Bidding'-state after bidding"
              (outputAuctionState txi o == Just (Bidding (BidderInfo bid bidder)))
          ; _ -> Pl.trace "There has to be exactly one continuing output to the validator itself" False
          }
