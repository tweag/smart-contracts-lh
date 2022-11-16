# Some proofs for the Auction contract

This directory contains some proofs for the [Auction contract][auction-contract].

[auction-contract]: https://github.com/tweag/plutus-libs/blob/main/examples/src/Auction.hs

The proofs ensure the absence of specific bugs.

* [Minswap.hs](./Minswap.hs) excludes the minswap vulnerability. This is
  the most commented module and should be the first read for those unfamiliar
  with Liquid Haskell.
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

    If a transaction succesfully consumes outputs from an auction
    and another script S, the seller, the bidders, and the auction
    validator are paid sufficiently for the purposes of the auction
    and the other script S.

Unfortunately the Auction contract allows this property to be
falsified.

The insight to exploit this vulnerability is to observe that
no particular datum is demanded of outputs paid to the seller
or the bidders. Thus, if a transaction works with multiple
contracts that need to make payments to the same wallets, the
Auction contract has no way to discern that the payments done
by the transaction to the seller and bidders are sufficient
given all the inputs that the transaction is consuming.

### Disproving double satisfaction for continuing output

Despite the aforementioned vulnerability, by the following argument,
it is not possible to steal from outputs paid to the validator.
First, each bid validator script is used only for a single auction.
This is guaranteed by the use of an NFT whose asset
class is a parameter to the script. Second, to have two
Auction validators accept a single bid, the output of the transaction
would need to be paid to the two different validator scripts,
which is impossible to do without paying each validator the
value of the bid.

For the `Bid` redeemer, which is the only redeemer producing continuing
outputs, the above argument reduces the presence of double satisfaction
to the presence of datum hijacking which has been disproved.

We could consider proving some of the above:

* The minting policy allows minting at most one token.
* If the minting policy accepts a transaction that mints one token,
  it must contain a specific input. This guarantees that the minting
  policy can't accept more than one transaction that mints.
* The Auction validator requires the NFT specified in its parameters
  to be in the inputs of the transaction.

### Disproving double satisfaction in an idealized contract

Let's suppose that the Auction validator demands in the datum of every
output the `TxOutRef` of the input being validated. The
`TxOutRef` identifies the output being consumed, and because
it can be consumed only once, different auctions would be forced
to pay different outputs with sufficient value to every involved
bidder, seller, and script.

One thing to prove in this setup is that the validator only accepts
the transaction if the outputs contain the aforementioned `TxOutRef`.

## Transaction level properties

The following properties together would ensure that no sequence of
transactions can lead to value paid by participants to end up locked
up indefinetely in unconsumable outputs, or to end up paid to other
actors than the seller or the bidders.

### Non-stealing

The following properties guarantee that the values of outputs paid to the
validator stay with the seller, the highest bidder or the Auction validator
after every transaction that spends them. This is an invariant first
established by the transaction that creates an Auction. Then every other
transaction that successfully consumes an output preserves this invariant.

Properties (1), (2), and (3) establish the existence of expected outputs;
while property (4) establishes that there are still as many outputs as
expected when a transaction consumes outputs paid to more than one Auction
validator.

1. **Absence of datum hijacking**
   Before the bidding deadline, any transaction successfully consuming an
   output from the Auction validator has a single output paid back to the
   same validator which contains both the bid and the lot.

2. Before the bidding deadline, any transaction successfully consuming an
   output from the Auction validator has an output paying the old bid to
   the old bidder.

3. After the bidding deadline, any transaction successfully consuming an output
   from the Auction validator has either:
    * outputs paying the lot to the seller if there was no bid, or
    * outputs paying a bid to the seller and outputs paying the lot to a bidder

4. **Absence of double satisfaction** as stated in the previous section.

### Spendability

The following property together with property (3) of the previous section
guarantee spendability of outputs paid to the validator. Said otherwise, the
contract doesn't lock values forever. This is an invariant first established
by the transaction that creates an Auction. Then every other transaction that
successfully consumes an output preserves the invariant.

    "absence of datum hijacking" with the additional requirement that the
    output is seller-and-bidder spendable.

We define a seller-spendable output as one for which there exists a transaction
signed only by the seller which succesfully consumes the output after the
deadline.

We define a bidder-spendable output as one for which there exists a transaction
signed only by a bidder which successfully consumes the output before the
bidding deadline, and there exists a transaction only signed by the bidder
which successfully consumes the output after the deadline.
