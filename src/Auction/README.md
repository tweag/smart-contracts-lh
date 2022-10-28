# Some proofs for the Auction contract

This directory contains some proofs for the [Auction contract][auction-contract].

The proofs ensure the absence of specific bugs.

* [Minswap.hs](./Minswap.hs) excludes the minswap vulnerability
* [MinswapNew.hs](./MinswapNew.hs) shows how Liquid Haskell fails when
  the implementation has the minswap bug.
* [DatumHijacking.hs](./DatumHijacking.hs) excludes the datum hijacking vulnerability
* [Spendability.hs](./Spendability.hs) attempts a proof of spendability

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
to the presence of datum hijacking which has been disproved.

We could still consider proving a few of these assumptions:

* The minting policy allows minting at most one token.
* If the minting policy accepts a transaction that mints one token,
  it must contain a specific input. This guarantees that the minting
  policy can't accept more than one transaction that mints.

[auction-contract]: https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs

## Transaction level properties

The following properties together would ensure that value can't be stolen
or locked indefinitely. Some of them can still be checked in the
specification of validators, other properties demand a proof of spendability,
and absence of double satisfaction requires combinig specs of the minting
policy and the Auction validator.

### Non-stealing

The following properties guarantee that the values of the transaction stay
with the seller and the highest bidder.

1. **Absence of datum hijacking**
   Before the bidding deadline, any transaction with an Auction input with
   bid redeemer which is accepted by the Auction validator has
   a unique output paying the bid and the lot to the validator.

2. Before the bidding deadline, any transaction with an Auction input with
   bid redeemer which is accepted by the Auction validator has
   an output paying the old bid to the old bidder.

3. **Absence of double satisfaction** as stated in the previous section.

### Spendability

The following properties guarantee spendability of outputs paid to the validator.
Said otherwise, the contract doesn't lock values forever.

1. Like "absence of datum hijacking" with the additional requirement that the
   output is seller-and-bidder spendable[1].

2. After the bidding deadline, any transaction with an Auction input which is
   accepted by the Auction validator has either:
    * outputs paying the lot to the seller if there was no bid, or
    * outputs paying a bid to the seller and outputs paying the lot to a bidder

[1] We define a seller-spendable output as one for which there exists a transaction
signed only by the seller which spends the output and is accepted by the validator
with hammer redeemer after the deadline.

We define a bidder-spendable output as one for which there exists a transaction
signed only by a bidder which spends it and is accepted by the validator
with bid redeemer before the bidding deadline, and there exists a transaction only signed by
the seller which spends it and is accepted by the validator with hammer redeemer
after the deadline.

