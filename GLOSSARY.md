# Glossary

- **Kernel:** Lean's small type checker that verifies every proof term.
- **Tactic:** a command that builds part of a proof, such as `simp`, `omega` or `induction`.
- **`sorry`:** placeholder for a missing proof; introduces the axiom `sorryAx`.
- **`#print axioms`:** command listing the axioms a declaration depends on.
- **Mathlib:** the community mathematics library for Lean 4.
- **Lake:** Lean's build tool and package manager.
- **Invariant:** a property that holds initially and is preserved by every transition.
- **Inductive invariant:** an invariant strong enough to be proved preserved by a single step.
- **Model gap:** the difference between the system modelled in Lean and the real implementation.
- **Soundness (circuit):** every witness satisfying the constraints yields the intended output.
- **Underconstrained circuit:** a circuit whose constraints admit unintended witnesses.
- **`ZMod p`:** Mathlib's integers modulo `p`; a field when `p` is prime.
- **Aeneas:** tool translating safe Rust into functional models for Lean and other provers.
- **Verus:** a Rust verifier using SMT solvers and specifications written in Rust syntax.
