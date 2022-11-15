{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | This module pretends to prove with Liquid Haskell that a variant
-- of the Auction contract in [1] doesn't have the minswap bug [2].
--
-- This variant, however, does have the minswap bug. We force LH to
-- accept the implementation with unsafe directives in the function 'amnt'.
--
-- [1] https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs
-- [2] https://www.tweag.io/blog/2022-03-25-minswap-lp-vulnerability/
module Auction.MinswapNew where

import qualified Data.ByteString -- import needed to avoid LH crashes

import qualified Plutus as Pl

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-cons" @-}


{-@ reflect noMinswap @-}
noMinswap
  :: Pl.ScriptContext -- ^ The context of the minting policy. It give access to
                      -- the information about the pending transaction.
  -> Pl.TokenName
  -> Maybe Integer  -- ^ The amount of tokens to mint or burn. We use @Maybe Integer@
                    -- because it composes better with the values we have in specifications.
  -> Bool
noMinswap ctx tokenName (Just amount) =
    case Pl.scriptContextPurpose ctx of
      Pl.Minting currencySymbol ->
        Pl.flattenValue (Pl.txInfoMint (Pl.scriptContextTxInfo ctx))
        ==
        [(currencySymbol, tokenName, amount)]
      _ ->
        False
noMinswap ctx tokenName Nothing = False

{-@
mkPolicy
  :: p:PolicyParams
  -> Pl.Address
  -> { ctx:Pl.ScriptContext | is$Plutus.Minting (Pl.scriptContextPurpose ctx) }
  -> { v:Bool |
       v =>
         noMinswap ctx (pThreadTokenName p) (Just 1)
         || noMinswap ctx (pThreadTokenName p) (Just (-1))
     }
@-}
mkPolicy :: PolicyParams -> Pl.Address -> Pl.ScriptContext -> Bool
mkPolicy (PolicyParams tName lotOref lot) validator ctx
  | amnt ctx tName == 1 =
      Pl.traceIfFalse
        "Lot UTxO not consumed"
        (any (\i -> Pl.txInInfoOutRef i == lotOref) $ Pl.txInfoInputs txi)
  | amnt ctx tName == (-1) = True
  | otherwise = False
  where
    txi = Pl.scriptContextTxInfo ctx
    Pl.Minting me = Pl.scriptContextPurpose ctx

    token :: Pl.Value
    token = Pl.singleton me tName 1

-- | @amnt@ returns the amount of tokens that a transaction wants to mint with a
-- particular asset class.
--
-- We use "assume" and "ignore" below to force LH to swallow it, because we have
-- asked in the specification that no other tokens are minted, and this is not
-- the case for the current implementation.
{-@
assume amnt
  :: { ctx:Pl.ScriptContext | is$Plutus.Minting (Pl.scriptContextPurpose ctx) }
  -> tName:Pl.TokenName
  -> { v:Integer | v != 0 => noMinswap ctx tName (Just v) }
ignore amnt
@-}
amnt :: Pl.ScriptContext -> Pl.TokenName -> Integer
amnt ctx tName =
      foldr
        ( \(cs, tn, a) n ->
            if cs == Pl.ownCurrencySymbol ctx && tn == tName
              then n + a
              else n
        )
        0
        $ Pl.flattenValue (Pl.txInfoMint txi)
  where
    txi = Pl.scriptContextTxInfo ctx

{-@
measure Plutus.flattenValue :: Pl.Value -> [(Pl.CurrencySymbol, Pl.TokenName, Integer)]
assume Pl.flattenValue
  :: x:Pl.Value -> {v:[(Pl.CurrencySymbol, Pl.TokenName, Integer)] | Plutus.flattenValue x = v }
@-}



--------------------------------------------------
-- Auxiliary definitions
--------------------------------------------------

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

outputAuctionState :: Pl.TxInfo -> Pl.TxOut -> Maybe AuctionState
outputAuctionState txi o = undefined

-- | All data the minting policy of the thread token needs to
-- know. These are known after the opening transaction
data PolicyParams = PolicyParams
  { -- | TokenName of the thread token
    pThreadTokenName :: Pl.TokenName,
    -- | outref of the utxo the seller spent the lot from
    pLotOutRef :: Pl.TxOutRef,
    -- | lot of the auction
    pLot :: Pl.Value
  }

{-@

data PolicyParams = PolicyParams
  { pThreadTokenName :: Pl.TokenName,
    pLotOutRef :: Pl.TxOutRef,
    pLot :: Pl.Value
  }

@-}

{-@ reflect isJust @-}
isJust :: Maybe a -> Bool
isJust Just{} = True
isJust _ = False
