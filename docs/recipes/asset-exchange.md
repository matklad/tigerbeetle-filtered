# Asset Exchange

Distinct [`ledger`](../reference/accounts.md#ledger) values typically denote distinct assets
or currencies. Transfers between pairs of accounts with different `ledger`s are
[not permitted](../reference/operations/create_transfers.md#accounts_must_have_the_same_ledger).

Instead, asset exchange (i.e. currency conversion) is implemented by creating two
[atomically linked](../reference/transfers.md#flags.linked)
different-ledger transfers between two pairs of same-ledger accounts.

A simple asset exchange involves four accounts:

  - A _source account_ `A₁`, on ledger `1`.
  - A _destination account_ `A₂`, on ledger `2`.
  - A _source liquidity account_ `L₁`, on ledger `1`.
  - A _destination liquidity account_ `L₂`, on ledger `2`.

and two linked transfers:

  - A transfer `T₁` from the _source account_ to the _source liquidity account_.
  - A transfer `T₂` from the _destination liquidity account_ to the _destination account_.

Both liquidity accounts belong to the same entity (e.g. a bank or exchange).
The transfer amounts vary according to the exchange rate.

## Example

Consider sending `$100` from account `A₁` (denominated in USD) to account `A₂` (denominated in INR).
Assuming an exchange rate of `$1.00 = ₹82.42135`, `$100.00 = ₹8242.135`:

| Ledger | Credit Account | Debit Account |  Amount | `flags.linked` |
| -----: | -------------: | ------------: | ------: | -------------: |
|    USD |           `A₁` |          `L₁` |   10000 |           true |
|    INR |           `L₂` |          `A₂` | 8242135 |          false |

- Amounts are [represented as integers](./fractional-amounts.md).
- Because both liquidity accounts belong to the same entity, the entity does not lose money on
  the transaction.
  - If the exchange rate is precise, the entity breaks even.
  - If the exchange rate is not precise, the application should round in favor of the liquidity
    account to deter arbitrage.
- Because the two transfers are linked together, they will either both succeed or both fail.

## Spread

In the above example, the liquidity provider breaks even. A fee (i.e. spread) can be included in the
`linked` chain as a separate transfer from the source account to the source liquidity account
(`A₁` to `L₁`).

This is preferable to simply modifying the exchange rate in the liquidity provider's favor because
it implicitly records the exchange rate and spread at the time of the exchange — information that
cannot be derived if the two are combined.