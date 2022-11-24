{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
module Plutus where

{-@ LIQUID "--ple" @-}
{-@ LIQUID "--exact-data-cons" @-}

import Data.List (find)
import qualified Data.Map as Map
import Data.ByteString (ByteString)

newtype TokenName = TokenName { unTokenName :: BuiltinByteString }
  deriving Eq

newtype Value = Value { getValue :: Map.Map CurrencySymbol (Map.Map TokenName Integer) }
  deriving Eq

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
  deriving (Eq, Ord)

type POSIXTimeRange = Interval POSIXTime

data TxInInfo = TxInInfo
    { txInInfoOutRef   :: TxOutRef
    , txInInfoResolved :: TxOut
    }
{-@
data TxInInfo = TxInInfo
    { txInInfoOutRef   :: TxOutRef
    , txInInfoResolved :: TxOut
    }

data TxOut = TxOut {
    txOutAddress   :: Address,
    txOutValue     :: Value,
    txOutDatumHash :: Maybe DatumHash
    }

@-}

data TxOut = TxOut {
    txOutAddress   :: Address,
    txOutValue     :: Value,
    txOutDatumHash :: Maybe DatumHash
    }
  deriving Eq

newtype DatumHash =
    DatumHash BuiltinByteString
  deriving Eq

datumHash :: Datum -> DatumHash
datumHash = undefined

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

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> PubKeyHash -> Bool
txSignedBy txi k = case find ((==) k) (txInfoSignatories txi) of
    Just _  -> True
    Nothing -> False

-- | Emit the given 'BuiltinString' only if the argument evaluates to 'False'.
{-@
reflect traceIfFalse
traceIfFalse :: BuiltinString -> x:Bool -> { v:Bool | v = x }
@-}
traceIfFalse :: BuiltinString -> Bool -> Bool
traceIfFalse str a = if a then True else trace str False

{-@
reflect trace
trace :: BuiltinString -> x:a -> { v:a | v = x }
@-}
trace :: BuiltinString -> a -> a
trace _ x = x

-- instance IsString BuiltinString where
--  fromString = BuiltinString . Data.Text.pack

instance Semigroup Value where
    (<>) = undefined

geq :: Value -> Value -> Bool
geq = undefined


-- | An interval of @a@s.
--
--   The interval may be either closed or open at either end, meaning
--   that the endpoints may or may not be included in the interval.
--
--   The interval can also be unbounded on either side.
data Interval a = Interval { ivFrom :: LowerBound a, ivTo :: UpperBound a }
  deriving (Eq, Ord)

data Extended a = NegInf | Finite a | PosInf
  deriving (Eq, Ord)

-- | Whether a bound is inclusive or not.
type Closure = Bool

data LowerBound a = LowerBound (Extended a) Closure
  deriving (Eq, Ord)

data UpperBound a = UpperBound (Extended a) Closure
  deriving (Eq, Ord)

-- | @a `contains` b@ is true if the 'Interval' @b@ is entirely contained in
--   @a@. That is, @a `contains` b@ if for every entry @s@, if @member s b@ then
--   @member s a@.
contains :: Ord a => Interval a -> Interval a -> Bool
contains (Interval l1 h1) (Interval l2 h2) = l1 <= l2 && h2 <= h1

to :: a -> Interval a
to s = Interval (LowerBound NegInf True) (upperBound s)

upperBound :: a -> UpperBound a
upperBound a = UpperBound (Finite a) True

{-@ ignore lovelaceValueOf @-}
lovelaceValueOf :: Integer -> Value
lovelaceValueOf = error "undefined lovelaceValueOf" -- TH.singleton adaSymbol adaToken

{-@ ignore valuePaidTo @-}
valuePaidTo :: TxInfo -> PubKeyHash -> Value
valuePaidTo ptx pkh = error "undefined valuePaidTo" -- mconcat (pubKeyOutputsAt pkh ptx)

{-@ ignore valueLockedBy @-}
-- | Get the total value locked by the given validator in this transaction.
valueLockedBy :: TxInfo -> ValidatorHash -> Value
valueLockedBy ptx h = error "undefined valueLockedBy"

{-@ ignore assetClassValue @-}
-- | A 'Value' containing the given amount of the asset class.
assetClassValue :: AssetClass -> Integer -> Value
assetClassValue (AssetClass (c, t)) i = error "undefined assetClassValue"

-- | Get the validator and datum hashes of the output that is curently being validated
{-@ ignore ownHashes @-}
ownHashes :: ScriptContext -> (ValidatorHash, DatumHash)
ownHashes (findOwnInput -> Just TxInInfo{txInInfoResolved=TxOut{txOutAddress=Address (ScriptCredential s) _, txOutDatumHash=Just dh}}) = (s,dh)
ownHashes _ = error "Lg" -- "Can't get validator and datum hashes"

-- | Get the hash of the validator script that is currently being validated.
ownHash :: ScriptContext -> ValidatorHash
ownHash p = fst (ownHashes p)

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Maybe TxInInfo
findOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs}, scriptContextPurpose=Spending txOutRef} =
    find (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs
findOwnInput _ = Nothing
