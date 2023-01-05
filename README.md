This repository contains experimental proofs for smart contracts.
The proofs are built with Liquid Haskell.

Build and verify with
```
stack --nix build
```

You might drop the `--nix` argument if `z3` is already in your PATH.

At the moment there are some [proofs](src/Auction) for an auction contract.
