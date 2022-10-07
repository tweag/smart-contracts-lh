This repository contains experimental proofs for smart contracts.
The proofs are built with Liquid Haskell.

There is [a pitch][pitch] motivating these experiments.

Build and verify with
```
stack build
```

At the moment there is only [one proof][noMinswap] of the absence of minswap in auctions.

[noMinswap]: https://github.com/tweag/smart-constracts-lh/blob/main/src/Auction/Minswap.hs
[pitch]: https://github.com/tweag/fm-meta/pull/13
