# Summary of changes for run 6d267076-09fe-4f5a-a819-6f666ea3a47f
I formalized all main theorems and definitions from `6_double_successor_memo.tex` (Chapter 6: Finite Generation at Double Successors) into two new Lean 4 files that compile successfully against the existing project:

### New files created

**`RequestProject/DoubleSuccMemo/Defs.lean`** — Definitions (240 lines, no sorries):
- `IsCPartition` — c-partition of a function (clopen partition where each restriction is centered)
- `OmegaRegularSet` — the test set W(α) = {k_λ} ∪ {ωh | h ∈ C(α)}
- `IsOmegaRegularAt` — ω-regularity at a point
- `IsLump` — a lump (g, y) where f_{(g,y)} fails ω-regularity
- `IsFineCPartition` — fine c-partition (no lumps, all parts of rank > λ)
- `IsPseudoCentered` — pseudo-centered function (single cocenter, all parts equivalent)
- `IsStronglySolvable` — strongly solvable function at y
- `IsSolvableFun` — solvable function with a fine c-partition

**`RequestProject/DoubleSuccMemo/Theorems.lean`** — Theorem statements (374 lines, 11 sorry'd theorems):
1. `refining_dissolves_lump` — **Lemma 6.1** (RefiningBy1): Dissolving lumps by refining c-partitions
2. `gobbling_less_than_lambda` — **Lemma 6.2** (gobblingLessThanLambda): Large centered pieces absorb small pieces
3. `existence_fine_partitions` — **Proposition 6.3** (ExistenceFinePartitions): FG(<α) implies existence of fine c-partitions
4. `vertical_theorem` — **Theorem 6.4** (VerticalTheorem): Structure of pseudo-centered functions
5. `diagonal_theorem` — **Theorem 6.5** (DiagonalTheorem): Structure of strongly solvable functions
6. `solvable_decomposition` — **Theorem 6.6** (SolvableDecomposition): Decomposing fine c-partitions into solvable pieces
7. `solvable_lambda_plus_one` — **Proposition 6.7** (solvablelambda+1): Statement S(λ) for limit/null λ
8. `FG_for_solvable` — **Theorem 6.8** (FiniteGenerationForSolvable): Finite generation for solvable functions
9. `FG_at_double_successors` — **Theorem 6.9** (FGatdoublesuccessors): The main inductive step FG(<α+2) ⟹ FG(≤α+2)
10. `preciseStructureThm_combined` — Combined Precise Structure Theorem: FG(α) for all α < ω₁
11. `bqo_scattered_combined` — BQO consequence for scattered continuous functions

All definitions and theorem statements type-check and are consistent with the project's existing conventions (using `ContinuouslyReduces`, `ContinuouslyEquiv`, `CBRank`, `FiniteGeneration`, etc. from earlier chapters). The proofs are left as `sorry` — these are deep results whose formal proofs would require substantial additional infrastructure.

# Summary of changes for run 40233a37-8f29-419f-b0f0-818542bbac9c
## Formalization of `5_precise_struct_memo.tex` — Precise Structure

I created two new Lean files formalizing the main theorems from Chapter 5 of the memoir on continuous reducibility:

### `RequestProject/PreciseStructMemo/Defs.lean` — Definitions (0 sorries)

Contains all core definitions from Chapter 5:
- **`WedgeFun`** — the wedge operation `⋁(f₀, …, fₖ | f_{k+1})`, the third and final operation on functions introduced in Chapter 5
- **`WedgeDomComponent`** / **`WedgeDom`** — domain of the wedge
- **`IsDominatedBy`** / **`DominationEquiv`** — domination order on sets of functions
- **`InScatteredClass`**, **`InCBLevel`**, **`InCBLevelLE`**, **`InCBLevelLT`**, **`InCBLevelInterval`** — predicates for CB-rank level membership
- **`FiniteGeneration`** — the statement FG(α): every function in 𝒞_α is continuously equivalent to a finite gluing of generators
- **`FiniteGeneration_below`** / **`FiniteGeneration_le`** — FG(<α) and FG(≤α)
- **`OmegaFun`** — the omega operation ω f

### `RequestProject/PreciseStructMemo/Theorems.lean` — Theorems (20 statements, 1 fully proved)

Contains formalizations of 20 main results from Chapter 5, organized into three sections:

**Proved:**
- `wedge_not_injective` (Fact 5.3, Item 2) — The wedge is not injective when k > 0

**Stated (with sorry):**
- *Wedge operation properties:* `wedge_preserves_continuity`, `wedge_CBrank`, `wedge_upper_bound`, `wedge_domination_equiv`, `disjointification_lemma`
- *Finite generation at successors of limits:* `infiniteEmbedOmegaStronger`, `intertwine_reductions`, `intertwine_reductions_omega_centered`, `omega_centered_to_component`, `maxFun_limit_to_component`, `diagonal_for_lambda_plus_one`, `FG_at_successor_of_limit`
- *Generators and the Precise Structure Theorem:* `alreadyKnownGenerators_1`, `generators_finite`, **`preciseStructureThm`** (the main result: 𝒞_α is finitely generated for every α < ω₁), `FG_base_cases`, `FG_implies_FG_succ_limit`, `FG_le_implies_interval_gen`, `FG_below_implies_bqo`, `FG_below_implies_locally_centered`, `FG_below_centered_classification`

Both files compile successfully and build on the existing project infrastructure (definitions from Chapters 1–4).

# Formalization of `5_precise_struct_memo.tex` — Precise Structure

## Files Created

### `RequestProject/PreciseStructMemo/Defs.lean` — Definitions (fully compiles, 0 sorries)

Contains all core definitions from Chapter 5:

- **`WedgeDomComponent`** — the domain components of the wedge operation
- **`WedgeDom`** — the full domain of the wedge (as a gluing)
- **`WedgeFun`** — the wedge operation `⋁(f₀, …, fₖ | f_{k+1})`, implementing:
  - `(i) ⌢ 0^ω ↦ 0^ω` for `i ≤ k`
  - `(i) ⌢ (0)^j ⌢ (1) ⌢ x ↦ (0)^j ⌢ (1) ⌢ (i) ⌢ f_i(x)` for `i ≤ k`
  - `(k+1+i) ⌢ x ↦ (0)^i ⌢ (1) ⌢ (k+1) ⌢ f_{k+1}(x)`
- **`IsDominatedBy`** / **`DominationEquiv`** — domination order on sets of functions
- **`InScatteredClass`** — membership in the class `𝒞` of scattered continuous functions
- **`InCBLevel`** / **`InCBLevelLE`** / **`InCBLevelLT`** / **`InCBLevelInterval`** — CB-rank level predicates
- **`FiniteGeneration`** — the statement `FG(α)`: every function in `𝒞_α` is continuously equivalent to a finite gluing of generators
- **`FiniteGeneration_below`** / **`FiniteGeneration_le`** — `FG(<α)` and `FG(≤α)`
- **`OmegaFun`** — the omega operation `ω f = ⊔_{n ∈ ℕ} f`

### `RequestProject/PreciseStructMemo/Theorems.lean` — Main Theorems (compiles, 1 theorem fully proved, 19 stated with sorry)

Contains formalizations of 20 main results from Chapter 5:

**Fully proved (1 theorem):**

1. **`wedge_not_injective`** (Fact 5.3, Item 2) — If `k > 0`, the wedge is not injective (because `(0) ⌢ 0^ω` and `(1) ⌢ 0^ω` both map to `0^ω`).

**Stated with sorry (19 theorems), organized by section:**

**Section 1 — The Wedge Operation (§5.1):**
- `wedge_preserves_continuity` (Fact 5.3, Item 1) — Wedge preserves continuity
- `wedge_CBrank` (Fact 5.3, Item 3) — CB-rank formula for wedge
- `wedge_upper_bound` (Proposition 5.5) — Wedge as upper bound criterion
- `wedge_domination_equiv` (Corollary 5.6) — Domination-equivalent verticals give equivalent wedges
- `disjointification_lemma` (Lemma 5.7) — Disjointification / wedge as lower bound

**Section 2 — Finite Generation at Successors of Limits (§5.2):**
- `infiniteEmbedOmegaStronger` (Lemma 5.9) — Stronger version of InfiniteEmbedOmega
- `intertwine_reductions` (Lemma 5.10) — Intertwining reductions for ω
- `intertwine_reductions_omega_centered` (Lemma 5.11) — Intertwining reductions for ω with centered functions
- `omega_centered_to_component` (Lemma 5.11, Item 1) — ω g ≤ f_i for some component
- `maxFun_limit_to_component` (Lemma 5.11, Item 2) — k_λ ≤ f_i for some component
- `diagonal_for_lambda_plus_one` (Lemma 5.12) — Diagonal lemma for λ+1
- `FG_at_successor_of_limit` (Theorem 5.13) — FG at successor of limit

**Section 3 — The Generators (§5.3):**
- `alreadyKnownGenerators_1` (Fact 5.16, Item 1) — 𝒢(1) = {ℓ₁, ω ℓ₁}
- `generators_finite` (Proposition 5.17, Item 3) — Generators are finite
- `preciseStructureThm` (Theorem 5.18) — **The Precise Structure Theorem**: every function in 𝒞_α is finitely generated
- `FG_base_cases` (Proposition 5.20, base) — FG(0), FG(1), FG(λ) for limit λ
- `FG_implies_FG_succ_limit` (Proposition 5.20, Item 1) — FG(<λ) ⟹ FG(λ+1)
- `FG_le_implies_interval_gen` (Proposition 5.20, Item 2) — FG(≤α) ⟹ interval generation
- `FG_below_implies_bqo` (Proposition 5.20, Item 3) — FG(<α) ⟹ BQO on 𝒞_{<α}
- `FG_below_implies_locally_centered` (Proposition 5.20, Item 4) — FG(<α) ⟹ locally centered
- `FG_below_centered_classification` (Proposition 5.20, Item 5) — Classification of centered functions

Both files compile successfully.
