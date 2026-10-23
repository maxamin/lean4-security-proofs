# Arithmetic, Overflow and Smart Contract Logic

Arithmetic bugs are among the most expensive in smart contracts: unchecked overflows, rounding in the wrong direction, precision loss in share calculations, and accounting that does not balance. Lean is well suited to proving arithmetic facts, because its `omega` tactic decides linear arithmetic over integers and naturals, and Mathlib provides deeper number theory when needed. This chapter models 256-bit arithmetic and simple contract accounting, and proves the properties auditors care about.

## Modelling machine words

Lean's `Nat` is unbounded, which is wrong for EVM arithmetic. Two common models:

| Model | How | When to use |
|---|---|---|
| `Nat` with explicit bound | define `WORD := 2^256`, add hypotheses `a < WORD` | readable, works with `omega` |
| Fixed-width types | Lean's `UInt8` to `UInt64`, `BitVec 256` | closer to hardware; `decide` or `bv_decide` for small facts |

Lean core has `BitVec n` and fixed-width `UIntN` types; for example `(200 : UInt8) + 100 = 44` is provable by `decide`, showing wrap-around. For 256-bit reasoning, the `Nat`-with-bound model plus `omega` is usually the clearest.

## Checked addition

Solidity 0.8 and later revert on overflow by default. Model it with `Option`:

```lean
def WORD : Nat := 2 ^ 256

def checkedAdd (a b : Nat) : Option Nat :=
  if a + b < WORD then some (a + b) else none

theorem checkedAdd_sound (a b r : Nat) (h : checkedAdd a b = some r) :
    r = a + b ∧ r < WORD := by
  unfold checkedAdd at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · contradiction
```

If the call succeeds, the result is the true mathematical sum and fits in a word. That is the guarantee code reviewers want when they see `a + b` in modern Solidity.

## Wrapping addition and overflow detection

Older code, `unchecked` blocks and some assembly use wrapping arithmetic, then detect overflow with a check such as `require(c >= a)`. We can prove that check is correct:

```lean
def wrapAdd (a b : Nat) : Nat := (a + b) % WORD

theorem wrap_detect (a b : Nat) (ha : a < WORD) (hb : b < WORD)
    (hov : WORD ≤ a + b) : wrapAdd a b < a := by
  unfold wrapAdd
  have hsub : (a + b) % WORD = a + b - WORD := by
    rw [Nat.mod_eq_sub_mod hov, Nat.mod_eq_of_lt (by omega)]
  omega
```

Whenever the true sum overflows, the wrapped result is smaller than `a`, so `c >= a` catches it. A companion lemma (an exercise) shows that without overflow, `c >= a` holds, so the check never rejects valid additions.

## Conservation of value

Accounting invariants are the heart of DeFi auditing. A minimal two-account ledger:

```lean
structure Ledger where
  alice : Nat
  bob   : Nat

def transfer (l : Ledger) (amt : Nat) : Option Ledger :=
  if amt ≤ l.alice then some { alice := l.alice - amt, bob := l.bob + amt } else none

theorem transfer_conserves (l l' : Ledger) (amt : Nat)
    (h : transfer l amt = some l') : l'.alice + l'.bob = l.alice + l.bob := by
  unfold transfer at h
  split at h
  · cases h; simp only; omega
  · contradiction
```

The balance check `amt ≤ l.alice` matters: Lean's natural-number subtraction truncates at zero, so without the check `alice - amt` would be `0` and value would be created. Try deleting the `if` and watch the proof fail. That truncation behaviour is itself a lesson: models must not hide bugs through convenient semantics.

For real tokens, balances are a map from addresses to amounts and the invariant is "sum of balances equals total supply". With Mathlib, balances can be modelled as a finitely supported function and sums as `Finset.sum`; the proof structure is the same, with more lemmas about sums. (Not compiled for this book; Mathlib's API names change over time, so check current documentation.)

## Rounding direction

Vault share calculations are a common source of value leaks: depositing rounds shares down, withdrawing rounds assets down, and getting either direction wrong lets users extract value in small increments. A Lean statement that captures the safe direction for deposits:

- shares minted = `assets * totalShares / totalAssets` (floor division)
- theorem: `shares * totalAssets ≤ assets * totalShares`, meaning the depositor never receives more than their fair share.

`omega` cannot prove facts involving products of two variables, so such proofs use lemmas like `Nat.div_mul_le_self` from core or Mathlib. This is where most of the real effort in arithmetic proofs goes.

## Connecting to real contracts

The model gap is real here. The Lean definitions above are hand-written. To tie proofs to deployed code, pair them with:

- property-based tests in Foundry that check the same invariants on the real contract;
- symbolic tools (see **neurosymbolic-contract-verification**) that check the bytecode;
- a review step that compares each Lean definition with the Solidity source line by line.

## Worked example

Prove the arithmetic lemmas and find the bug the balance check prevents. Executed while writing this book with Lean 4.35.0; the code in this chapter is the exact file that compiled.

1. Put `WORD`, `checkedAdd`, `checkedAdd_sound`, `wrapAdd`, `wrap_detect`, `Ledger`, `transfer`, `transfer_conserves` and `example : (200 : UInt8) + 100 = 44 := by decide` into `Arith.lean`.
2. Run `lean Arith.lean`. It compiled with no errors.
3. Change `transfer` to always return `some { alice := l.alice - amt, bob := l.bob + amt }` and adapt the proof to `unfold transfer at h; cases h; simp only; omega`. `omega` failed, reporting a possible counterexample with `amt - alice ≥ 1`: value is created when `amt > alice`.
4. Run `#eval (transfer ⟨5, 0⟩ 10).map (fun l => (l.alice, l.bob))` with the broken definition to see the concrete counterexample. It printed `some (0, 10)`: five tokens became ten.
5. Restore the check and confirm the proof passes again.

All five steps were executed with Lean 4.35.0. The companion lemma in exercise 1 was also checked (`rw [Nat.mod_eq_of_lt h]` followed by `omega`), so treat it as a solvable warm-up.

## Common pitfalls

- Proving facts over unbounded `Nat` that are false for 256-bit words.
- Relying on truncated `Nat` subtraction, which silently hides underflow bugs.
- Expecting `omega` to handle non-linear arithmetic (products of variables).
- Proving conservation for a two-account toy and assuming it holds for the real mapping-based contract.
- Not stating the rounding direction explicitly in the theorem.

## Exercises

1. Prove the companion lemma: if `a + b < WORD` then `wrapAdd a b ≥ a`.
2. Model a three-account ledger with transfers between any pair and prove conservation.
3. State and prove a floor-division rounding lemma for vault deposits using `Nat.div_mul_le_self` (search core Lean or Mathlib for the exact name and form).

## Further reading

- [Lean core documentation for `BitVec` and `omega`](https://lean-lang.org/doc/reference/latest/)
- [Mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
- **neurosymbolic-contract-verification**, **defi-economic-attack-simulation**
