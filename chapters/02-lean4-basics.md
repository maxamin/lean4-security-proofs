# Lean 4 Basics for Security Engineers

This chapter teaches just enough Lean 4 to model systems and prove simple properties. It assumes you can program in some language and know what a function and a data type are. It skips most of the mathematics and focuses on the tools you will use in later chapters: inductive types, recursive functions, `#eval`, theorem statements and a handful of tactics.

## Definitions and evaluation

```lean
def double (n : Nat) : Nat := n + n

example : double 21 = 42 := rfl

def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs
```

`Nat` is the type of natural numbers (unbounded, no overflow). `List Nat` is a list. Functions defined by pattern matching must be total: Lean checks that every case is handled and that recursion terminates. That totality is useful in security models because it rules out undefined cases by construction.

`#eval sumList [1, 2, 3]` runs the function. `example : double 21 = 42 := rfl` is a tiny proof: `rfl` (reflexivity) works when both sides compute to the same value.

## Propositions and proofs

A theorem is a definition whose type is a proposition. Proving it means constructing a term of that type, usually with tactics.

```lean
theorem sumList_append (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih => simp [sumList, ih]; omega
```

Read it as: for all lists `xs` and `ys`, the sum of the concatenation is the sum of the parts. The proof goes by induction on `xs`. The `nil` case simplifies by the definition of `sumList`. In the `cons` case the induction hypothesis `ih` is available, `simp` rewrites with it, and `omega` closes the remaining linear arithmetic.

## Tactics you will use most

| Tactic | Use |
|---|---|
| `rfl` | both sides compute to the same value |
| `decide` | proposition is decidable and small enough to evaluate |
| `simp [defs]` | rewrite and simplify using definitions and simp lemmas |
| `omega` | linear arithmetic over `Nat` and `Int` (also handles `%` and `/` by literals) |
| `unfold f` | replace `f` by its definition |
| `cases x` | split on the constructors of an inductive value |
| `induction xs with ...` | structural induction |
| `intro h` | introduce a hypothesis |
| `constructor`, `left`, `right`, `exact` | build conjunctions, pick disjuncts, supply terms |
| `rcases h with h1 \| h2` | destructure hypotheses |
| `split at h` | split on an `if` or `match` inside a hypothesis |
| `simp_all` | simplify all hypotheses and the goal together |

Combinators like `cases s <;> simp [step]` apply the second tactic to every goal produced by the first, which is how you dispatch large case analyses on protocol states in one line.

## Inductive types for security models

Protocol messages, states and roles are naturally inductive types:

```lean
inductive Msg where
  | hello | keyEx | finished | appData | alert
  deriving DecidableEq, Repr
```

`deriving DecidableEq` lets Lean decide equality between messages automatically, so `decide` and `simp` can reason about them. `Repr` lets `#eval` print values.

## Structures

Records with named fields model ledgers, configurations and contract state:

```lean
structure Ledger where
  alice : Nat
  bob   : Nat
```

## `Option` for failure

Operations that can fail, such as a transfer with insufficient balance, return `Option`. `some x` is success and `none` is failure (a revert). Proving properties about the `some` case is the standard pattern for "if this call succeeds, then ...".

## Checking assumptions

```lean
#print axioms sumList_append
```

prints the axioms the theorem depends on. For `sumList_append`, Lean 4.35.0 reported `[propext, Quot.sound]`, which are standard axioms used by `simp`. If you ever see `sorryAx`, part of the proof is missing.

## Projects and Mathlib

For a single file, `lean File.lean` is enough. For a project with dependencies, use Lake, Lean's build tool: `lake new myproof` creates a project, and adding Mathlib as a dependency (Mathlib's README documents the current procedure, including downloading prebuilt caches with `lake exe cache get`) gives access to finite fields, modular arithmetic and much more. Mathlib is large; use its cache rather than building it from source.

## Worked example

Prove a property of a simple function end to end. Executed while writing this book with Lean 4.35.0; the code below is the exact file that compiled.

1. Create `Basics.lean` with `double`, `sumList` and `sumList_append` as shown above, and add `#print axioms sumList_append` at the end.
2. Run `lean Basics.lean`. It produced no errors and printed the axiom list `[propext, Quot.sound]`.
3. Replace the `cons` case with only `simp [sumList]` and rerun. Expect an unsolved goal involving `ih`; read the goal display to see what is missing.
4. Restore the proof, then add `#eval sumList [1, 2, 3]` and confirm it prints `6`.
5. Write a new function `maxList` and state (but try to prove yourself) that every element of the list is at most `maxList`.

## Common pitfalls

- Using `Nat` where the real system uses fixed-width integers, and proving things that are false with overflow (chapter 4 fixes this).
- Writing `simp` without the definitions it needs (`simp [f]`), then concluding a true goal is unprovable.
- Forgetting `deriving DecidableEq` on enumerations and fighting equality proofs by hand.
- Ignoring the goal display; Lean shows exactly what remains to prove.
- Building Mathlib from source instead of using its cache.

## Exercises

1. Prove `∀ n, double n % 2 = 0` with `unfold` and `omega`.
2. Define `count : Msg → List Msg → Nat` and prove that `count m (xs ++ ys) = count m xs + count m ys`.
3. Create a Lake project with Mathlib as a dependency following its README, and `#check` the type `ZMod 7` to confirm Mathlib is available.

## Further reading

- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Lean community website and Zulip](https://leanprover-community.github.io/)
