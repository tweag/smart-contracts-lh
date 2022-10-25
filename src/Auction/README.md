# Some proofs for the Auction contract

This directory contains some proofs for the [Auction contract][auction-contract].

The proofs ensure the absence of specific bugs.

* [Minswap.hs](./Minswap.hs) excludes the minswap vulnerability
* [MinswapNew.hs](./MinswapNew.hs) shows how Liquid Haskell fails when
  the implementation has the minswap bug.
* [DatumHijacking.hs](./DatumHijacking.hs) excludes the datum hijacking vulnerability

## Double satisfaction

Double satisfaction occurs when a single output of a
transaction satisfies the validators of two different inputs.
For instance, in the auction contract, it would be no good
if two auctions accepted a single bid, which would open an
opportunity to steal some of the value of one of the auctions.

Absence of double satisfaction could be expressed as follows:

    If a transaction bids for two auctions and the validators accept it,
    each auction validator is paid the expected amount.

In the auction contract it is not possible to falsify this condition.
First, each bid validator script is used only for a single auction.
This is guaranteed by the use of a unique NFT whose asset
class is a parameter to the script. Second, to have two
auctions accept a single bid, the output of the transaction
would need to be paid to the two different validator scripts,
which is impossible to do without paying each validator the
value of the bid.

The above argument reduces the presence of double satisfaction
to the presence of datum hijacking which has been proven to be
absent.

We could still consider proving a few of these assumptions:

* The minting policy allows minting at most one token.
* If the minting policy accepts a transaction that mints one token,
  it must contain a specific input. This guarantees that the minting
  policy can't accept more than one transaction that mints.

[auction-contract]: https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs

