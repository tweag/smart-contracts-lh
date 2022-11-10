{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}

-- | This module proves with Liquid Haskell that the Auction
-- contract in [1] doesn't have the minswap bug [2].
--
-- We had to take drastic measures to circumvent limitations in Liquid
-- Haskell for the only purpose of illustrating what a proof would look
-- like in an idealized world where the drastic measures aren't necessary.
--
-- [1] https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs
-- [2] https://www.tweag.io/blog/2022-03-25-minswap-lp-vulnerability/
module Auction.Minswap where

import qualified Data.ByteString -- import needed to avoid LH crashes

-- The Plutus definitions are copied in a local module. This allows us
-- to verify the contract without having to build all of the plutus
-- dependencies. A few integration issues would remain to be solved in
-- order to use the definitions as they are in the plutus packages.
import qualified Plutus as Pl

-- --ple enables the algorithm proof-by-logical-evaluation. This is
-- required for Liquid Haskell to automate the unfolding of functions
-- when writing proofs.
{-@ LIQUID "--ple" @-}

-- --exact-data-cons brings into scope field-selector functions and
-- constructor test functions for an ADT. For instance, given an ADT
-- like
--
-- > data ScriptPurpose
-- >   = Minting CurrencySymbol
-- >   | Spending TxOutRef
-- >   | Rewarding StakingCredential
-- >   | Certifying DCert
--
-- this flag allows LH to use @is$Minting :: ScriptPurpose -> Bool@
-- in proofs and specifications to express that a value must be
-- constructed with the @Minting@ data constructor.
--
-- In a similar way, field-selectors are produced, like
--
-- > lqdc##$select##Minting##1 :: ScriptPurpose -> CurrencySymbol
--
-- to access the field of the @Minting@ data constructor.
--
{-@ LIQUID "--exact-data-cons" @-}


-- | The minswap bug is about minting more tokens than intended. In the
-- case of the auction contract, we can make this statement more concrete
-- by restricting the tokens to belong to a single asset class. Therefore,
-- we write a predicate that holds for all transactions that only mint or
-- burn tokens with a particular asset class and amount, and do not allow
-- any other tokens to be burnt.
--
-- The @reflect@ directive below indicates that @noMinswap@ might be used
-- in specifications, and could be unfolded in proofs.
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
        flattenValueR (Pl.txInfoMint (Pl.scriptContextTxInfo ctx))
        ==
        [(currencySymbol, tokenName, amount)]
      _ ->
        False
noMinswap ctx tokenName Nothing = False

-- | @mkPolicy@ is the minting policy script. Similarly to @noMinswap@ it
-- checks that only a particular token is minted or burnt, but it also does
-- other things, like checking that the token is paid to a particular script.
--
-- In this experiment, we aren't concerned with the other checks that the
-- minting policy does, so the specification only focuses on checking that
-- the minswap bug is absent.
--
-- We say that the minswap bug is absent if whenever the minting policy
-- accepts the transaction, we can prove that our predicate 'noMinswap' holds.
--
-- Note that we require no preconditions on the inputs other than expecting
-- the context to hold a Minting purpose.
--
-- The bulk of this proof is done in the function 'amnt'. @mkPolicy@ starts
-- by invoking @amnt@. If @amnt@ returns a @Just@ value, its specification
-- establishes that the predicate @noMinswap@ holds, and therefore @mkPolicy@
-- is free to either accept or reject the transaction.
--
-- On the other hand, when @amnt@ returns @Nothing@, @mkPolicy@ is only allowed
-- to reject the transaction, and the user must convince LH that the transaction
-- is actually going to be rejected.
--
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
  | amnt == Just 1 =
      Pl.traceIfFalse
        "Lot UTxO not consumed"
        (any (\i -> Pl.txInInfoOutRef i == lotOref) $ Pl.txInfoInputs txi)
      && case filter
        (\o -> Pl.txOutAddress o == validator)
        (Pl.txInfoOutputs txi) of
        [o] ->
          Pl.traceIfFalse
            "Validator does not receive the lot and the thread token of freshly opened auction"
            (Pl.txOutValue o `Pl.geq` (lot <> token))
            && Pl.traceIfFalse
              "Validator not in 'NoBids'-state on freshly opened auction"
              (outputAuctionState txi o == Just NoBids)
        _ -> Pl.trace "There must be exactly one output to the validator on a fresh auction" False
  | amnt == Just (-1) = True
  | otherwise = False
  where
    txi = Pl.scriptContextTxInfo ctx

    Pl.Minting me = Pl.scriptContextPurpose ctx

    token :: Pl.Value
    token = Pl.singleton me tName 1

    -- @amnt@ returns the amount of tokens that a transaction wants to mint with a
    -- particular asset class, but only does so if the transaction only mints tokens
    -- of one asset class. The specification establishes this formally, and LH is
    -- able to prove it without further help.
    {-@ amnt :: { v:Maybe Integer | isJust v => noMinswap ctx tName v } @-}
    amnt :: Maybe Integer
    amnt =
      case flattenValueR (Pl.txInfoMint txi) of
        [(cs, tn, a)] | cs == Pl.ownCurrencySymbol ctx && tn == tName -> Just a
        _ -> Nothing

--------------------------------------------------
-- Limitations
--------------------------------------------------

-- In this proof we uncovered the following limitations
--
-- * liquid-base expects a version of base which is newer than the one provided by ghc-8.10.4.20210212.
--   LH sometimes depends on libraries like liquid-base or liquid-bytestring
--   which need to match the versions of the libraries used by a particular
--   version of ghc. This can make a challenge to support mutliple compiler
--   versions. We might be able to come up with a scheme were we can reuse
--   code across different versions of these libraries.
--
-- * data definitions need to be added to the logic
--   When specifications need to refer to ADTs, these types need to be
--   added to the logic. Liquid Haskell does not do this automatically.
--   Maybe we can have this done automatically, or otherwise, we need to come up
--   with ways to write libraries with the ADTs definitions that we need added.
--
-- * partial validators need to be totalized
--   If a validation script is supposed to produce an exception on
--   certain inputs, LH is unable to specify it. In order to reason with
--   these scripts, we would need to change them to make them total.
--
-- * need to write specs for the functions to manipulate Value
--   We will have to write specifications for the operations of Values to
--   do other proofs. Perhaps we don't need to prove that the
--   specifications are actually valid.
--
-- * augment the environment of error messages
--   When liquid haskell reports errors, it prints part of the environment
--   in which a constraint could not be proven. Sometimes relevant bindings
--   are omitted in the report. Ideally we would get all the relevant
--   information in the error without having to dive into file dumps.
--
-- * allow to reflect functions which call non-reflected functions
--   We have to introduce @flattenValueR@ only to be able to reflect @noMinswap@
--   Ideally, we wouldn't have to do this.
--
-- * redundant transitive imports are sometimes needeed to avoid crashes
--   For instance importing Data.ByteString as done in this module
--
-- * LH crashes when trying to use BuiltinString as defined in plutus.
--   We avoid this by making BuiltinString a synonim of String.
--

-- | @flattenValueR@ is a device we use to refer to flattening of values
-- in specifications, without having LH bring to the logic the actual
-- implementation of @flattenValue@. With an ideal LH, we would be able
-- to have the implementation of the minting policy refer to the original
-- @flattenValue@, and the specifications would use an uninterpreted
-- function like this @flattenValueR@.
--
-- The meaning of @flattenValueR@ doesn't play a role in the proof, and
-- therefore we can omit it in this particular case. It is up to the user
-- to ensure that @flattenValueR@ is used correctly in the definition of
-- @noMinswap@.
{-@
reflect flattenValueR
lazy flattenValueR
@-}
flattenValueR :: Pl.Value -> [(Pl.CurrencySymbol, Pl.TokenName, Integer)]
flattenValueR v = flattenValueR v


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
