# func_wqo_lean

A Lean 4 formalization of the memoir [*Continuous Reducibility is a Well-Quasi-Order on Continuous Functions*](https://arxiv.org/abs/2410.13150) by Raphaël Carroy and Yann Pequignot. 

## Overview

This project formalizes the main results of a memoir in descriptive set theory, proving that **continuous reducibility is a well-quasi-order (WQO)** — and in fact a **better-quasi-order (BQO)** — on natural classes of continuous functions.

**Continuous reducibility** is the quasi-order where `f ≤ g` if there exist continuous maps `σ` and `τ` such that `f = τ ∘ g ∘ σ`. It generalizes Wadge reducibility (where functions are characteristic functions of sets) to arbitrary continuous functions.

### Main theorems

| Theorem | Statement |
|---------|-----------|
| **Main Theorem 1** | Continuous reducibility is WQO on continuous functions from an analytic zero-dimensional space to a separable metrizable space. |
| **Main Theorem 2** | Continuous reducibility is WQO on continuous functions from a separable metrizable zero-dimensional space to a countable metrizable space. |
| **Main Theorem 3** | Continuous reducibility is WQO on *scattered* continuous functions from a zero-dimensional separable metrizable space to a metrizable space. |
| **BQO theorem** | All three main theorems hold with BQO in place of WQO. |

The central structural result driving the proof is:

> **Finite Generation:** For every countable ordinal `α`, the class `𝒞_α` of scattered continuous functions with Cantor–Bendixson rank exactly `α` is *finitely generated* under continuous equivalence and the gluing operation.

## Repository structure

The Lean source files in `RequestProject/` mirror the chapters of the memoir:

| Directory / File | Content |
|-----------------|---------|
| `IntroMemo.lean` | Core definitions (`ContinuouslyReduces`, `ScatteredFun`, `IsBetterQuasiOrder`) and statements of all main theorems |
| `PrelimMemo/` | Preliminary results: basics, the gluing operation, scattered spaces |
| `BaireSpace/` | General results about the Baire space `ℕ → ℕ`; generalised reducibility properties |
| `Bqo/` | BQO theory: Ramsey-type theorems, two-element BQO lemmas |
| `PointedGluing/` | The core of the proof — pointed gluing operation, General Structure theorem, max/min functions and their CB-rank bounds |
| `CenteredMemo/` | Centered functions and local centeredness |
| `PreciseStructMemo/` | Precise structure theorem for successor of limit ordinals |
| `DoubleSuccMemo/` | Double-successor case of finite generation |

The corresponding informal proofs are in the `.tex` files at the root of the repository (`1_intro_memo.tex` through `6_double_successor_memo.tex`).

## Key concepts

- **Cantor–Bendixson (CB) rank of a function:** The ordinal index at which the iterated CB derivative (restricting to points where `f` is not locally constant) stabilizes to the empty set. Scattered functions are exactly those with finite CB rank level sets.
- **Gluing:** The natural disjoint-union operation on functions (on both domain and codomain), used to build complex functions from simpler ones.
- **Pointed Gluing:** A refinement of gluing that "points" the pieces; the central operation in proving upper and lower bound results.
- **Max/Min functions:** Canonical representatives `MaxFun α` and `MinFun α` that are respectively maximum and minimum among functions of CB rank `α`.
- **General Structure theorem:** For a scattered function `g` with `CBRank g = η`, any scattered `f` with `CBRank f ≤ η` satisfies `f ≤ g`.

## Current proof status

The General Structure theorem (`PointedGluing/GeneralStructure.lean`) is fully formalized. This is the main result from Raphaël Carroy Carroy, *A quasi-order on continuous functions* (JSL, 2013).

The proof of twoBQO_of_twoBQO_levels that states that 
````
If 𝒞_β is 2-BQO for all β < ω₁, then ScatFun is 2-BQO
```
still needs to be formalized. It uses General Structure theorem and results on 2-BQOs about 2nLTm.

## Building

This project requires [Lean 4](https://leanprover.github.io/) and [Lake](https://github.com/leanprover/lake). It depends on [Mathlib4](https://github.com/leanprover-community/mathlib4) at `v4.28.0`.

```bash
# Install elan (Lean version manager) if needed
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# Fetch Mathlib cache (strongly recommended — avoids rebuilding Mathlib from source)
lake exe cache get

# Build the project
lake build
```

The Lean toolchain version is specified in `lean-toolchain` (`leanprover/lean4:v4.28.0`).


## Collaboration

Parts of this formalization were developed with assistance from [Aristotle (Harmonic)](https://aristotle.harmonic.fun) and  [Claude Code](https://claude.com/claude-code).

## License

See [LICENSE](LICENSE).
