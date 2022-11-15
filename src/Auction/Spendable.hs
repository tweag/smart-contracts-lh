{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | This module explores proving with Liquid Haskell that the Auction
-- outputs produced by the Auction contract [1] are spendable.
--
-- The proof requires reflecting the validator, so LH can unfold it
-- and prove that it accepts contexts with the new datum.
--
-- The proof is not complete due to some bug in LH. See the comments
-- above function 'checkOutput'.
--
-- [1] https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs
module Auction.Spendable where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-cons" @-}

import qualified Data.ByteString -- needed to avoid LH crash
import qualified Plutus as Pl
import Prelude hiding (const)
import Language.Haskell.Liquid.ProofCombinators (pleUnfold)

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

{-@
data StaticValParams = StaticValParams
  { bidDeadline' :: Pl.POSIXTime,
    minBid' :: Integer,
    lot' :: Pl.Value
  }
@-}

data ValParams = ValParams
  { staticValParams :: StaticValParams,
    -- | address of the seller
    seller :: Pl.PubKeyHash,
    threadTokenAssetClass :: Pl.AssetClass
  }
{-@
data ValParams = ValParams
  { staticValParams :: StaticValParams,
    seller :: Pl.PubKeyHash,
    threadTokenAssetClass :: Pl.AssetClass
  }
@-}

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
    case uniqueContinuingOutputWithDatum ctx datum of
      Just _ -> True
      _ -> False

{-@ reflect uniqueContinuingOutputWithDatum @-}
uniqueContinuingOutputWithDatum
    :: Pl.ScriptContext -> AuctionState -> Maybe Pl.TxOut
uniqueContinuingOutputWithDatum ctx datum = pleUnfold
    (case getContinuingOutputs ctx of
      [o] | outputAuctionState (Pl.scriptContextTxInfo ctx) o == Just datum ->
        Just o
      _ ->
        Nothing)

{-@
measure Auction.Spendable.getContinuingOutputs :: Pl.ScriptContext -> [Pl.TxOut]
assume getContinuingOutputs
  :: x:Pl.ScriptContext -> {v:[Pl.TxOut] | Auction.Spendable.getContinuingOutputs x = v }
@-}
getContinuingOutputs :: Pl.ScriptContext -> [Pl.TxOut]
getContinuingOutputs = undefined

{-@
measure Auction.Spendable.outputAuctionState :: Pl.TxInfo -> Pl.TxOut -> Maybe AuctionState
assume outputAuctionState
  :: x:Pl.TxInfo -> y:Pl.TxOut -> { v:Maybe AuctionState | Auction.Spendable.outputAuctionState x y = v }
@-}
outputAuctionState :: Pl.TxInfo -> Pl.TxOut -> Maybe AuctionState
outputAuctionState = undefined

{-@
measure Auction.Spendable.bidTimeRange :: ValParams -> Pl.POSIXTimeRange
assume bidTimeRange
  :: x:ValParams -> { v:Pl.POSIXTimeRange | Auction.Spendable.bidTimeRange x = v }
@-}
bidTimeRange :: ValParams -> Pl.POSIXTimeRange
bidTimeRange a = Pl.to (bidDeadline a)

bidDeadline :: ValParams -> Pl.POSIXTime
bidDeadline = bidDeadline' . staticValParams

{-@
measure Auction.Spendable.minBid :: ValParams -> Integer
assume minBid
  :: x:ValParams -> { v:Integer | Auction.Spendable.minBid x = v }
@-}
minBid :: ValParams -> Integer
minBid p = minBid' (staticValParams p)

{-@
measure Auction.Spendable.lot :: ValParams -> Pl.Value
assume lot
  :: x:ValParams -> { v:Pl.Value | Auction.Spendable.lot x = v }
@-}
lot :: ValParams -> Pl.Value
lot p = lot' (staticValParams p)

-- | Test that the value paid to the giv,en public key address is at
-- least the given value
receivesFrom :: Pl.TxInfo -> Pl.PubKeyHash -> Pl.Value -> Bool
receivesFrom txi who what = Pl.valuePaidTo txi who `Pl.geq` what

{-@
measure Auction.Spendable.receivesFrom :: Pl.TxInfo -> Pl.PubKeyHash -> Pl.Value -> Bool
assume receivesFrom
  :: x:Pl.TxInfo -> y:Pl.PubKeyHash -> z:Pl.Value -> { v:Bool | Auction.Spendable.receivesFrom x y z = v }
@-}

{-@
measure Plutus.ownHash :: Pl.ScriptContext -> Pl.ValidatorHash
assume Pl.ownHash :: x:Pl.ScriptContext -> { v:Pl.ValidatorHash | Plutus.ownHash x = v }
@-}

{-@
measure Plutus.contains :: Ord a => Pl.Interval a -> Pl.Interval a -> Bool
assume Pl.contains :: Ord a => x:Pl.Interval a -> y:Pl.Interval a -> { v:Bool | Plutus.contains x y = v }
@-}

{-@
measure Plutus.lovelaceValueOf :: Integer -> Pl.Value
assume Pl.lovelaceValueOf :: x:Integer -> { v:Pl.Value | Plutus.lovelaceValueOf x = v }
@-}

{-@
measure Plutus.geq :: Ord a => Pl.Value -> Pl.Value -> Bool
assume Pl.geq :: Ord a => x:Pl.Value -> y:Pl.Value -> { v:Bool | Plutus.geq x y = v }
@-}

{-@
measure Plutus.txSignedBy :: Pl.TxInfo -> Pl.PubKeyHash -> Bool
assume Pl.txSignedBy
  :: x:Pl.TxInfo -> y:Pl.PubKeyHash -> { v:Bool | Plutus.txSignedBy x y = v }
@-}

{-@
measure Plutus.valueLockedBy :: Pl.TxInfo -> Pl.ValidatorHash -> Pl.Value
assume Pl.valueLockedBy
  :: x:Pl.TxInfo -> y:Pl.ValidatorHash -> { v:Pl.Value | Plutus.valueLockedBy x y = v }
@-}

{-@
measure add :: Pl.Value -> Pl.Value -> Pl.Value
assume add
  :: x:Pl.Value -> y:Pl.Value -> { v:Pl.Value | add x y = v }
@-}
add :: Pl.Value -> Pl.Value -> Pl.Value
add = undefined

{-@
measure Plutus.assetClassValue :: Pl.AssetClass -> Integer -> Pl.Value
assume Pl.assetClassValue
  :: x:Pl.AssetClass -> y:Integer -> { v:Pl.Value | Plutus.assetClassValue x y = v }
@-}

{-@ reflect updCtx @-}
updCtx :: Pl.ScriptContext -> Integer -> Pl.PubKeyHash -> Pl.ScriptContext
updCtx ctx bid bidder =
  case uniqueContinuingOutputWithDatum ctx (Bidding (BidderInfo bid bidder)) of
    Nothing -> ctx
    Just o -> ctx
      { Pl.scriptContextTxInfo =
        (Pl.scriptContextTxInfo ctx)
          { Pl.txInfoInputs =
              replaceTxOut
                (spentOut (Pl.scriptContextPurpose ctx))
                o
                (Pl.txInfoInputs
                   (Pl.scriptContextTxInfo ctx)
                )
          }
      }

{-@ reflect replaceTxOut @-}
replaceTxOut :: Maybe Pl.TxOutRef -> Pl.TxOut -> [Pl.TxInInfo] -> [Pl.TxInInfo]
replaceTxOut i o [] = []
replaceTxOut i o (x:xs)
  | Just (Pl.txInInfoOutRef x) == i = x { Pl.txInInfoResolved = o } : xs
  | otherwise = x : replaceTxOut i o xs

{-@ reflect spentOut @-}
spentOut :: Pl.ScriptPurpose -> Maybe Pl.TxOutRef
spentOut (Pl.Spending o) = Just o
spentOut _ = Nothing

{-@ inline const @-}
const :: a -> b -> a
const a _ = a

{-@
reflect validBid
validBid
  :: auction:ValParams
  -> datum:AuctionState
  -> bid:Integer
  -> bidder:Pl.PubKeyHash
  -> ctx:Pl.ScriptContext
  -> { v:Bool
     | v => hasOnlyOneContinuingOutputWithDatum ctx (Bidding (BidderInfo bid bidder))
 //           && validBid auction datum bid bidder (updCtx ctx bid bidder)
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
   {-
      Pl.traceIfFalse
        "Bidding past the deadline is not permitted"
        (bidTimeRange auction `containsR` Pl.txInfoValidRange txi)
      &&
        Pl.traceIfFalse "Bid transaction not signed by bidder" (txi `txSignedBy` bidder)
      && Pl.traceIfFalse
          "Validator does not lock lot, bid, and thread token"
          ( valueLockedBy txi selfh
              `geq` ( lot auction `add` (lovelaceValueOfR bid
                        `add` assetClassValue (threadTokenAssetClass auction) 1)
                    )
          )
      && -}

          checkOutput ctx bid bidder
        {-
      && case datum of
          NoBids ->
            Pl.traceIfFalse "Cannot bid less than the minimum bid" (minBid auction <= bid)
          Bidding (BidderInfo lastBid lastBidder) ->
            Pl.traceIfFalse "Must bid more than the last bid" (lastBid < bid)
              && Pl.traceIfFalse
                "Last bidder is not paid back"
                (lastBidder `receives` lovelaceValueOf lastBid)
-}


-- Apparently, we need to tell LH the refinement type to infer for the code
-- that checks datum hijacking, otherwise, LH can't verify validBid.
--
-- Initially, checkOutput was inlined at the call site.

-- The specification of 'checkOutput' is rejected when we demand that
-- the produced datum is spendable
--
--     "checkOutput (updCtx ctx bid bidder) bid bidder"
--
-- LH is not able to prove it for some reason that needs to be debugged.
--
-- Using assume also causes the caller of checkOutput to fail.

{-@
reflect checkOutput
checkOutput
  :: ctx:Pl.ScriptContext
  -> bid:Integer
  -> bidder:Pl.PubKeyHash
  -> { v:Bool
     | v => hasOnlyOneContinuingOutputWithDatum ctx (Bidding (BidderInfo bid bidder))
   //         && checkOutput (updCtx ctx bid bidder) bid bidder
     }
@-}
checkOutput :: Pl.ScriptContext -> Integer -> Pl.PubKeyHash -> Bool
checkOutput ctx bid bidder =
  let txi = Pl.scriptContextTxInfo ctx
   in case getContinuingOutputs ctx of {
          [o] ->
             let hasExpectedDatum = (outputAuctionState txi o == Just (Bidding (BidderInfo bid bidder)))
              in -- TODO: PLE doesn't assume the "v =>" part of the predicate
                 -- and therefore it can't unfold uniqueContinuingOutputWithDatum
                 -- if we simplify this let expression.
                 if hasExpectedDatum then
                   True
                    `const`
                   lemmaGetContinuingOutputsUpdCtx
                     bid
                     bidder
                     ctx
                     o
                     (updCtx ctx bid bidder)
                    `const`
                   lemmaOutputAuctionStateUpdCtx
                     bid
                     bidder
                     ctx
                     o
                     (updCtx ctx bid bidder)
                 else
                   Pl.traceIfFalse
                     "Not in the correct 'Bidding'-state after bidding"
                     False

          ; _ -> Pl.trace "There has to be exactly one continuing output to the validator itself" False
          }

{-@
assume lemmaGetContinuingOutputsUpdCtx
  :: bid:Integer
  -> bidder:Pl.PubKeyHash
  -> ctx0:Pl.ScriptContext
  -> { o:Pl.TxOut | Just o = uniqueContinuingOutputWithDatum ctx0 (Bidding (BidderInfo bid bidder)) }
  -> { ctx1:Pl.ScriptContext
     | Pl.txInfoInputs (Pl.scriptContextTxInfo ctx1)
         =
            replaceTxOut
              (spentOut (Pl.scriptContextPurpose ctx0))
              o
              (Pl.txInfoInputs
                 (Pl.scriptContextTxInfo ctx0)
              )
       &&
         Pl.txInfoOutputs (Pl.scriptContextTxInfo ctx0)
           =
         Pl.txInfoOutputs (Pl.scriptContextTxInfo ctx1)
     }
  -> { getContinuingOutputs ctx0 = getContinuingOutputs ctx1
     }
@-}
lemmaGetContinuingOutputsUpdCtx
  :: Integer
  -> Pl.PubKeyHash
  -> Pl.ScriptContext
  -> Pl.TxOut
  -> Pl.ScriptContext
  -> ()
lemmaGetContinuingOutputsUpdCtx bid bidder ctx0 o ctx1 = ()


-- This lemma states that outputAuctionState yields the same result when
-- given the original ScriptContext and when given the ScriptContext of
-- the example transaction that should allow to spend the continuing
-- output.
--
-- It would be a choice of the programmer to leave the lemma as an assumption
-- or go through the trouble of proving it further, probably by introducing
-- further lemmas abount how the functions used by outputAuctionState deal
-- with the context.

{-@
assume lemmaOutputAuctionStateUpdCtx
  :: bid:Integer
  -> bidder:Pl.PubKeyHash
  -> ctx0:Pl.ScriptContext
  -> { o:Pl.TxOut | Just o = uniqueContinuingOutputWithDatum ctx0 (Bidding (BidderInfo bid bidder)) }
  -> { ctx1:Pl.ScriptContext
     | Pl.txInfoInputs (Pl.scriptContextTxInfo ctx1)
         =
            replaceTxOut
              (spentOut (Pl.scriptContextPurpose ctx0))
              o
              (Pl.txInfoInputs
                 (Pl.scriptContextTxInfo ctx0)
              )
       &&
         Pl.txInfoOutputs (Pl.scriptContextTxInfo ctx0)
           =
         Pl.txInfoOutputs (Pl.scriptContextTxInfo ctx1)
     }
  -> { outputAuctionState (Pl.scriptContextTxInfo ctx0) o = outputAuctionState (Pl.scriptContextTxInfo ctx1) o
     }
@-}
lemmaOutputAuctionStateUpdCtx
  :: Integer
  -> Pl.PubKeyHash
  -> Pl.ScriptContext
  -> Pl.TxOut
  -> Pl.ScriptContext
  -> ()
lemmaOutputAuctionStateUpdCtx bid bidder ctx0 o ctx1 = ()


-----------------------------------------------------
-- Limitations
-----------------------------------------------------
--
-- * When unfolding 'f' in 'v => f', PLE does not assume 'v'.
--   This is an inconvenient when v gives information necessary
--   to unfold 'f'. We could try to make PLE smarter for that case.
--
-- * Proving spendability requires lemmas on various functions to show
--   that they provide expected values when editing the context to
--   show that the validator can accept a transaction that uses the
--   new datum.
