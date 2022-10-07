{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Plutus where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-cons" @-}

import qualified Data.Map as Map
import Data.ByteString (ByteString)

newtype TokenName = TokenName { unTokenName :: BuiltinByteString }
  deriving Eq

newtype Value = Value { getValue :: Map.Map CurrencySymbol (Map.Map TokenName Integer) }

newtype CurrencySymbol = CurrencySymbol { unCurrencySymbol :: BuiltinByteString }
  deriving Eq

data BuiltinByteString = BuiltinByteString ByteString
  deriving Eq

data TxOutRef = TxOutRef {
    txOutRefId  :: TxId,
    txOutRefIdx :: Integer -- ^ Index into the referenced transaction's outputs
    }
  deriving Eq

newtype TxId = TxId { getTxId :: BuiltinByteString }
  deriving Eq

data ScriptContext = ScriptContext{scriptContextTxInfo :: TxInfo, scriptContextPurpose :: ScriptPurpose }

{-@
data ScriptContext = ScriptContext{scriptContextTxInfo :: TxInfo, scriptContextPurpose :: ScriptPurpose }

data ScriptPurpose
    = Minting CurrencySymbol
    | Spending TxOutRef
    | Rewarding StakingCredential
    | Certifying DCert
@-}

data ScriptPurpose
    = Minting CurrencySymbol
    | Spending TxOutRef
    | Rewarding StakingCredential
    | Certifying DCert

data StakingCredential
    = StakingHash Credential
    | StakingPtr Integer Integer Integer -- NB: The fields should really be Word64 / Natural / Natural, but 'Integer' is our only integral type so we need to use it instead.
  deriving Eq

data Credential
  = PubKeyCredential PubKeyHash -- ^ The transaction that spends this output must be signed by the private key
  | ScriptCredential ValidatorHash -- ^ The transaction that spends this output must include the validator script and be accepted by the validator.
  deriving Eq

newtype PubKeyHash = PubKeyHash { getPubKeyHash :: BuiltinByteString }
  deriving Eq

data TxInfo = TxInfo
    { txInfoInputs      :: [TxInInfo] -- ^ Transaction inputs
    , txInfoOutputs     :: [TxOut] -- ^ Transaction outputs
    , txInfoFee         :: Value -- ^ The fee paid by this transaction.
    , txInfoMint        :: Value -- ^ The 'Value' minted by this transaction.
    , txInfoDCert       :: [DCert] -- ^ Digests of certificates included in this transaction
    , txInfoWdrl        :: [(StakingCredential, Integer)] -- ^ Withdrawals
    , txInfoValidRange  :: POSIXTimeRange -- ^ The valid range for the transaction.
    , txInfoSignatories :: [PubKeyHash] -- ^ Signatures provided with the transaction, attested that they all signed the tx
    , txInfoData        :: [(DatumHash, Datum)]
    , txInfoId          :: TxId
    -- ^ Hash of the pending transaction (excluding witnesses)
    }

{-@

data TxInfo = TxInfo
    { txInfoInputs      :: [TxInInfo]
    , txInfoOutputs     :: [TxOut]
    , txInfoFee         :: Value
    , txInfoMint        :: Value
    , txInfoDCert       :: [DCert]
    , txInfoWdrl        :: [(StakingCredential, Integer)]
    , txInfoValidRange  :: POSIXTimeRange
    , txInfoSignatories :: [PubKeyHash]
    , txInfoData        :: [(DatumHash, Datum)]
    , txInfoId          :: TxId
    }

@-}

-- | POSIX time is measured as the number of milliseconds since 1970-01-01T00:00:00Z
newtype POSIXTime = POSIXTime { getPOSIXTime :: Integer }

-- type POSIXTimeRange = Interval POSIXTime
data POSIXTimeRange -- kept opaque for now

data TxInInfo = TxInInfo
    { txInInfoOutRef   :: TxOutRef
    , txInInfoResolved :: TxOut
    }

data TxOut = TxOut {
    txOutAddress   :: Address,
    txOutValue     :: Value,
    txOutDatumHash :: Maybe DatumHash
    }

newtype DatumHash =
    DatumHash BuiltinByteString


newtype Datum = Datum { getDatum :: BuiltinData  }

data BuiltinData -- PLC.Data -- kept opaque for now

data Address = Address{ addressCredential :: Credential, addressStakingCredential :: Maybe StakingCredential }
  deriving Eq

data DCert
  = DCertDelegRegKey StakingCredential
  | DCertDelegDeRegKey StakingCredential
  | DCertDelegDelegate
      StakingCredential
      -- ^ delegator
      PubKeyHash
      -- ^ delegatee
  | -- | A digest of the PoolParams
    DCertPoolRegister
      PubKeyHash
      -- ^ poolId
      PubKeyHash
      -- ^ pool VFR
  | -- | The retiremant certificate and the Epoch N
    DCertPoolRetire PubKeyHash Integer -- NB: Should be Word64 but we only have Integer on-chain
  | -- | A really terse Digest
    DCertGenesis
  | -- | Another really terse Digest
    DCertMir

newtype ValidatorHash =
    ValidatorHash BuiltinByteString
  deriving Eq

newtype AssetClass = AssetClass { unAssetClass :: (CurrencySymbol, TokenName) }

-- | Convert a value to a simple list, keeping only the non-zero amounts.
flattenValue :: Value -> [(CurrencySymbol, TokenName, Integer)]
flattenValue v = goOuter [] (Map.toList $ getValue v)
  where
    goOuter acc []             = acc
    goOuter acc ((cs, m) : tl) = goOuter (goInner cs acc (Map.toList m)) tl

    goInner _ acc [] = acc
    goInner cs acc ((tn, a) : tl)
        | a /= 0    = goInner cs ((cs, tn, a) : acc) tl
        | otherwise = goInner cs acc tl

-- | Make a 'Value' containing only the given quantity of the given currency.
singleton :: CurrencySymbol -> TokenName -> Integer -> Value
singleton c tn i = Value (Map.singleton c (Map.singleton tn i))

{-@ reflect isMinting @-}
isMinting :: ScriptPurpose -> Bool
isMinting Minting{} = True
isMinting _ = False

-- | The 'CurrencySymbol' of the current validator script.
{-@
reflect ownCurrencySymbol
ownCurrencySymbol :: {ctx:ScriptContext | isMinting (scriptContextPurpose ctx) } -> CurrencySymbol
@-}
ownCurrencySymbol :: ScriptContext -> CurrencySymbol
ownCurrencySymbol ScriptContext{scriptContextPurpose=Minting cs} = cs

-- data BuiltinString = BuiltinString Text
type BuiltinString = String

-- | Emit the given 'BuiltinString' only if the argument evaluates to 'False'.
traceIfFalse :: BuiltinString -> Bool -> Bool
traceIfFalse str a = if a then True else trace str False

trace :: BuiltinString -> a -> a
trace _ x = x

-- instance IsString BuiltinString where
--  fromString = BuiltinString . Data.Text.pack

instance Semigroup Value where
    (<>) = undefined

geq :: Value -> Value -> Bool
geq = undefined
