# Summary of changes for run 9033399e-0d36-4ef3-b8fb-0a24a52e8da8
Successfully resolved the `sorry` in `theorem minFun_is_minimum` in `RequestProject/PointedGluing/MinFun.lean`.

**Proof strategy:**

The theorem states that for any scattered continuous function `f : A → ℕ → ℕ` with `(CBLevel f α).Nonempty` and `α < ω₁`, the minimum function `MinFun α` continuously reduces to `f`.

The proof works by reducing the general case to the already-proven simple case (`minFun_is_minimum_simple`):

1. **Find an isolated point**: Since `CBLevel f α` is nonempty and `f` is scattered, the isolated locus of `f` on `CBLevel f α` is nonempty. Pick a point `x` in this isolated locus — this ensures `x ∈ CBLevel f α` but `x ∉ CBLevel f (succ α)`.

2. **Get a clopen neighborhood**: Using `isolatedLocus_gives_simple_neighborhood` and `baire_exists_clopen_subset_of_open`, find a clopen set `V` in Baire space containing `x` such that `CBLevel f (succ α) ∩ V = ∅` and `f` is constant on `V ∩ CBLevel f α`.

3. **Apply the simple case**: The restriction `f_V` to `A_V = A ∩ V` satisfies all hypotheses of `minFun_is_minimum_simple` at level `α`: nonemptiness of `CBLevel f_V α` (via `CBLevel_AW_iff` and `CBLevel_open_restrict`), emptiness of `CBLevel f_V (succ α)`, and constancy. This gives `MinFun α ≤ f_V`.

4. **Compose with inclusion**: Since `A_V ⊆ A`, compose the reduction with the natural inclusion to get `MinFun α ≤ f`.

Two helper lemmas were introduced and proved:
- `minFun_reduces_to_subtype_reduces`: composing a reduction to a subtype restriction with the inclusion
- `isolated_point_exists_in_CBLevel`: extracting an isolated point from a nonempty CB level of a scattered function

The proof compiles without any `sorry` and uses only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

# Summary of changes for run 8dfdd5d1-db5f-4c56-b366-51ed33733673
## Summary

I made substantial progress on proving `minFun_is_minimum_simple` in `RequestProject/PointedGluing/MinFun.lean`.

### What was accomplished

**New helper file created:** `RequestProject/PointedGluing/MinFunLocalHelpers.lean` containing 7 fully-proved helper lemmas (no sorries):

1. `exists_ray_cbrank_gt` — Given the supremum of ray CB ranks equals α and β < α, finds N with ray CB rank > β.
2. `exit_ordinal_of_ray_point` — Shows a point in a ray of a simple function has exit ordinal < α.
3. `simple_restrict_clopen` — Shows simplicity is preserved when restricting to a smaller clopen set.
4. `compose_reduction_from_subtype` — Composes a reduction through a subtype to produce σ mapping into U with separation.
5. `find_ray_point` — The core construction: given f simple at α with β < α, finds a point p with p.val ∈ V, exit ordinal γ with β ≤ γ < α, and f(p) N ≠ y N. This includes a fully proved `cb_transfer` lemma that transfers CB levels between isomorphic domain types.
6. `decompose_at_point` — Given a point with exit ordinal γ, produces a clopen neighborhood W ⊆ V with f|_W simple and range separation.

**Main proof structure (MinFun.lean):** The proof of `minFun_local_condition'` is structured with steps 1-3 fully proved:
- Step 1: Extract open set V from the subspace topology
- Step 2: Use `find_ray_point` to locate point p with the right CB properties
- Step 3: Use `decompose_at_point` to get a clopen piece W with SimpleFun and range separation

### What remains

**One sorry in `minFun_local_condition'`** (line 321): This captures the final steps of the proof, which involve:
1. Converting `SimpleFun` between isomorphic domain types ({a : ↑A | a.val ∈ W} vs ↑{z | z ∈ A ∧ z ∈ W})
2. Showing δ < α and β ≤ δ (mathematically straightforward)
3. Applying the induction hypothesis and MinFun_monotone
4. Converting ContinuouslyReduces between the isomorphic domain types
5. Showing IsClosed {z | z N ≠ y N}

The difficulty is purely technical (Lean type coercions between subtypes of ℕ → ℕ and subtypes of subtypes), not mathematical. The mathematical argument is complete.

**`minFun_is_minimum'`** (line 565) also remains as sorry — this is a separate, more general theorem that was already sorry'd before.

### Files modified
- `RequestProject/PointedGluing/MinFun.lean` — Added import, restructured proof of `minFun_local_condition'`
- `RequestProject/PointedGluing/MinFunLocalHelpers.lean` — New file with 7 fully-proved helper lemmas

# Summary of changes for run 15392725-625f-4e91-9e75-4db68a4b1271
## Summary

I made substantial progress on proving `minFun_is_minimum_simple` in `RequestProject/PointedGluing/MinFun.lean`. The theorem states that the minimum function `MinFun α` continuously reduces to any simple scattered function with CB level α nonempty and CB level (succ α) empty.

### What was accomplished

**Main proof structure (complete):** The proof of `minFun_is_minimum_simple` is fully structured using strong induction on ordinals, with three cases:

1. **Base case (α = 0):** Uses the existing `minFun_zero_reduces` lemma.

2. **Successor case (α = succ γ):** Converts `MinFun (succ γ)` to a pointed gluing via `MinDom_succ` and `PointedGluingFun_id`, then applies the existing `pointedGluing_lower_bound` theorem.

3. **Limit case (α is a limit ordinal):** Similarly converts via `MinDom_limit` and applies `pointedGluing_lower_bound`.

**Helper lemmas (proved):**
- `pgl_val_to_minFun_succ'`: Converts reductions from the PointedGluingSet formulation to the MinFun formulation (successor case)
- `pgl_val_to_minFun_limit'`: Same for the limit case  
- `pgl_fun_id_eq_val'`: Shows `PointedGluingFun` with identity equals `val`

### What remains

One helper lemma `minFun_local_condition'` remains as `sorry`. This lemma encapsulates the core local condition for the pointed gluing lower bound: for each index and open neighborhood U of x, constructing the reduction data (σ, τ) from `MinDom β` to `A` with σ mapping into U and f(x) separated from the closure of the range. The proof sketch is documented in the code and involves:
1. Restricting f to U and analyzing ray CB ranks
2. Decomposing the ray into simple pieces using the decomposition lemma
3. Finding a piece with sufficient CB rank
4. Applying the induction hypothesis and composing reductions

The difficulty is primarily technical rather than mathematical — it requires careful handling of Lean's subtype coercions when working with functions on subtypes of subtypes of the Baire space, while the CB analysis lemmas in the project are stated for `Set (ℕ → ℕ)` domains.

### Files modified
- `RequestProject/PointedGluing/MinFun.lean`: Added the proof structure, helper lemmas, and import of `Scattered.Decomposition`

# Summary of changes for run d859e2d4-83fe-4855-b798-1ff8fe0e86be
I resolved the `sorry`s in `RequestProject/PointedGluing/MinFun.lean` as follows:

## Completed: `pointedGluing_lower_bound'` (fully proved)

This theorem had 5 `sorry`s that were all resolved:

1. **Threading lemma (`lseq p ≤ kseq q`)**: The original construction used `∀ n, ∃ k l m σ τ, GoodData ...` followed by `choose`, which lost the cross-step relationship `kseq(n+1) = lseq(n)`. I restructured the construction to use explicit `Nat.rec` recursion:
   - Defined a `mkStep` function that produces `(l, m, σ, τ)` given `(n, prevl)` with `l ≥ prevl + 1`
   - Built `kseq` via `Nat.rec 0 (fun n prev => (mkStep n prev).choose)`
   - This preserves `lseq n = kseq (n+1)` by definition, making `kseq` strictly monotone
   - The threading lemma then follows from `kseq_strictMono.monotone`

2. **hsep** (`f x ∉ closure (f '' An n)`): Proved using `hclos n` (closure disjoint from `cylfx (mseq n)`) and `hfx_cylfx` (f x ∈ cylfx (mseq n)).

3. **hrelclop** (`IsRelativeClopenPartition`): 
   - Disjointness: For `i < j`, threading gives `f '' An j ⊆ cylfx (mseq i)`, and `hclos i` gives `f '' An i ∩ cylfx (mseq i) = ∅`.
   - Relatively open: Each piece is separated by clopen sets (finite intersections of `cylfx` neighborhoods).

4. **hconv** (`SetsConvergeTo An x`): Since `An n ⊆ cyl (kseq n)` and `kseq n ≥ n`, for any open U ∋ x, eventually `An n ⊆ U`.

5. **hred** (ContinuouslyReduces): Used `σ_n n` and `τseq n` with continuity from `hσc n` and equation from `hcomm n`.

## Remaining: 2 `sorry`s

Two deep theorems remain unproved:

- **`minFun_is_minimum_simple`** (line 273): States that MinFun α continuously reduces to any simple scattered function f with CB rank exactly α+1. The proof requires transfinite induction, ray function decomposition, regular sequences, and CB rank analysis — infrastructure that is partially present but incomplete in the project.

- **`minFun_is_minimum'`** (line 440): States that MinFun α continuously reduces to any scattered function with (CBLevel f α).Nonempty. This builds on `minFun_is_minimum_simple` via decomposition into simple pieces.

Both theorems reference key infrastructure (ray functions restricted to ray sets, regular ordinal sequences, cofinal sequence properties) that would need substantial additional development to formalize.

## Cleanup

- Removed a large (~435 line) commented-out block of old code to keep the file manageable.
- Fixed linter warnings (unused simp args, `simpa` → `simp`).
- The project builds successfully with only the two `sorry` warnings.

# Summary of changes for run cd470e87-384b-4841-9212-acaec6f847a8
Successfully resolved all sorry's in `RequestProject/PointedGluing/LowerBoundLemma.lean`. The file originally contained 10 sorry placeholders within the theorem `pointedGluing_lower_bound_lemma'`. Here's a summary of what was done:

**Helper lemmas added above the main theorem:**
1. `sigma_cont_on_pieces` — proves that σ is continuous on each ray block (piece). The proof works by showing σ agrees with a continuous composition on each piece using `pgl_sigma_eq_on_block`, `continuous_stripZerosOne`, and `firstNonzero_eq_of_block`.

2. `tau_global_continuousOn` — proves ContinuousOn τ_global on range(f ∘ σ). The proof splits into two cases:
   - For points in ⋃ In n: uses that τ_global restricted to the union equals the continuous τ, combined with `ContinuousWithinAt.mono_of_mem_nhdsWithin`.
   - For the base point f x: uses `continuousWithinAt_pi` to reduce to coordinatewise convergence, then shows each coordinate j is eventually 0 near f x (because points near f x must lie in In(m) with m > j, making prependZerosOne m (...) j = 0).

**Fixes within the main theorem:**
- **τi continuity** (was 2 sorry's): Fixed by providing the constant value `n` and using `hτi_n` to show τi equals n on each piece In n.
- **ContinuousOn on U** (was 3 sorry's): Restructured to use `codRestrict`/`subtype_mk` composition approach, factoring through the subtype ↑UI.
- **Sequential condition** (was 1 sorry): Proved that τ_global(f(σ(zk k))) ∈ nbhd zeroStream N by showing τi picks the block index and using `prependZerosOne_head_eq_zero`.
- **ContinuousOn derivation** (was 1 sorry): Now uses `tau_global_continuousOn` helper.
- **Basepoint equation** (was 1 sorry): Proved by unfolding `PointedGluingFun` at zeroStream.
- **Non-basepoint equation** (was 1 sorry): Proved by combining `pointedGluingFun_eq_on_block`, `hτi_n`, and `hτ_n_eq`.

All proofs compile cleanly and depend only on standard axioms (propext, Classical.choice, Quot.sound).

# Summary of changes for run b37ceb33-6ff8-4c6b-a63e-c1b2b713f1ae
## Summary of Changes to MinFun.lean

I worked on resolving the `sorry`s in `RequestProject/PointedGluing/MinFun.lean`. The file contained several issues that needed to be addressed before the main theorems could be attempted.

### Issues Fixed (compilation errors and bugs)

1. **Fixed pre-existing build error in `Decomposition.lean`** (line 185): Added missing `[TopologicalSpace Y]` instance to `cb_rank_of_clopen_union`, which was blocking the entire build chain.

2. **Fixed type error in `minFun_zero_reduces`**: Changed `fun _ => x` to `fun _ => ⟨x, hx⟩` to correctly construct a subtype element for the reduction map σ.

3. **Fixed parse error**: The standalone docstring `/-- **Proposition (Minfunctions). Minimum functions.** -/` before `lemma minFun_is_minimum_simple` was not attached to any declaration. Converted to a regular comment.

4. **Fixed type error in `minFun_is_minimum_simple` statement**: The hypothesis `(∃ y ∈ Baire, (hy_simple : ...))` was incorrect because `Baire` is a type alias (`ℕ → ℕ`), not a set, so `y ∈ Baire` doesn't typecheck. Fixed to `(∃ y : ℕ → ℕ, ∀ x ∈ CBLevel f α, f x = y)`.

5. **Added missing import**: Added `import RequestProject.PointedGluing.MinFunLowerBound` to make `baire_cylinder_mem_nhds`, `baire_subspace_cylinder_mem_nhds`, and `pgl_lower_bound_step` available.

### Corrected equation direction in `pointedGluing_lower_bound'`

The original `hloc` hypothesis had the equation `∀ z, f (σ z) = τ (g i z)`, which represents `f ∘ σ` being computed from `g_i` (i.e., a reduction in the wrong direction). The mathematical intent (matching `pgl_lower_bound_step` in `MinFunLowerBound.lean`) is `∀ z, (g i z : ℕ → ℕ) = τ (f (σ z))`, which says `g_i` reduces to `f` locally. The statement was corrected with a docstring explaining the change.

### Remaining Sorries (3)

The three remaining sorry'd theorems are deep research-level results:

1. **`pointedGluing_lower_bound'`** (Proposition 3.11 - Pointed gluing as lower bound): Requires constructing recursive sequences of cylinder neighborhoods with controlled separation, defining clopen sets with pairwise disjoint images under f, and proving the continuous reduction. The proof outline is documented in comments.

2. **`minFun_is_minimum_simple`**: Requires transfinite induction on ordinals, using the pointed gluing lower bound and CB-rank regularity results.

3. **`minFun_is_minimum'`**: Requires transfinite induction combined with the decomposition lemma for scattered functions.

These theorems involve sophisticated constructions combining transfinite induction, Baire space topology, and the Cantor-Bendixson analysis developed throughout the project. Multiple attempts were made with the theorem proving infrastructure, but the proofs are beyond the current reach of automated methods.

### Build Status

The full project builds successfully with `lake build` (8059 jobs, no errors). All changes are backward-compatible and don't introduce any new axioms.

# Summary of changes for run 78e7edd3-3e77-4ca9-870f-eaa8e5f42a0a
## Refactoring Summary

The project has been refactored into a cleaner modular structure with minimized imports and split large files. All changes compile successfully with `lake build`.

### 1. Split Large Files

**`PrelimMemo/Scattered.lean` (1601 → 3 sub-files + re-export):**
- `PrelimMemo/Scattered/CBAnalysis.lean` (524 lines) — NowhereLocllyConstant, CB derivative, CB rank, scattered ↔ empty perfect kernel, reduction & CB monotonicity
- `PrelimMemo/Scattered/NonScattered.lean` (704 lines) — Non-scattered embedding theorem (Theorem 2.5), Cantor scheme construction
- `PrelimMemo/Scattered/Decomposition.lean` (411 lines) — SimpleFun definition, first reduction theorem, zero-dim/disjoint union, decomposition lemma
- `PrelimMemo/Scattered.lean` (11 lines) — Re-export module that imports all three sub-files, so existing `import RequestProject.PrelimMemo.Scattered` statements continue to work

**`PointedGluing/PointedGluingUpperBound.lean` (1134 → 2 sub-files + re-export):**
- `PointedGluing/PointedGluingUpperBound/BasicProperties.lean` (496 lines) — Fact 3.1 (continuity/injectivity preservation), Proposition 3.2 (CB rank), Fact 3.3 (gluing ≤ pointed gluing)
- `PointedGluing/PointedGluingUpperBound/UpperBound.lean` (593 lines) — Lemma 3.4 (sufficient condition for continuity), Proposition 3.5 (upper bound), scatteredness preservation
- `PointedGluing/PointedGluingUpperBound.lean` (9 lines) — Re-export module

### 2. Minimized Imports

Eliminated ~150 redundant import lines across all files. Every file now imports only the minimal set of direct dependencies needed — typically 1–2 imports each instead of the previous 6–15 per file. Key changes:

- Removed `import Mathlib` from all files except `IntroMemo.lean` and `Main.lean` (Mathlib is transitively available through the import chain)
- Removed all redundant transitive project-local imports (e.g., if a file imports `PointedGluing.ClopenPartitionReduces` which transitively provides `PointedGluing.Defs`, the direct `Defs` import was removed)
- Fixed a hidden redundant import: `PrelimMemo/Gluing.lean` was importing `Scattered` despite not using any of its definitions — changed to import only `PrelimMemo.Basic`

### 3. Removed Empty File

Deleted `PrelimMemo/blackboard.lean` (0 lines, no content).

### Import Chain (simplified)

```
IntroMemo → Mathlib
PrelimMemo.Basic → IntroMemo
PrelimMemo.GenRedProp → Basic
PrelimMemo.Gluing → Basic
PrelimMemo.Scattered.CBAnalysis → GenRedProp
PrelimMemo.Scattered.NonScattered → CBAnalysis
PrelimMemo.Scattered.Decomposition → NonScattered + Gluing
PointedGluing.Defs → Gluing
PointedGluing.CBRankHelpers → Defs + Scattered.CBAnalysis
  ↓ (linear chain through CB helpers, upper bound, max/min, etc.)
PointedGluing.Theorems → MaxFunMaximum
CenteredMemo → PointedGluing (Defs + Theorems)
PreciseStructMemo → CenteredMemo.Theorems
DoubleSuccMemo → PreciseStructMemo.Theorems
```

All files are now under 720 lines (down from 1601 max). The build produces the same warnings and `sorry` count as before — no functional changes were made.

# Summary of changes for run 0e303e45-f561-4194-bb1d-74d20ee39a7b
## Summary of Progress on MinFun.lean

### What was accomplished

**Proved `pointedGluing_lower_bound_lemma`** (Lemma 3.10 — Pointed Gluing as Lower Bound): This is the most substantial theorem in the file. The proof constructs σ and τ witnessing the continuous reduction, and verifies:
- Continuity of σ (using the `sufficient_cond_continuity` lemma with block decomposition)
- ContinuousOn of τ on the relevant range (two-case analysis: at the basepoint f(x) and away from it)
- The functional equation PointedGluingFun = τ ∘ f ∘ σ

The proof was decomposed into four helper lemmas in a new file `RequestProject/PointedGluing/MinFunHelpers.lean`:
1. `pgl_lower_bound_equation` — the equation part
2. `pgl_lower_bound_sigma_seq` — the sequential convergence condition for σ
3. `pgl_sigma_eq_on_block` — σ agrees with σ_n on each open block
4. `pgl_lower_bound_sigma_cont_on_U` — ContinuousOn σ on the non-zero-stream set
5. `pgl_lower_bound_tau_cont` — ContinuousOn τ on the range

All five helper lemmas are fully proved (no sorry).

### What remains (2 sorries)

1. **`pointedGluing_lower_bound`** (Proposition 3.11 — line 102): This requires constructing a sequence of clopen sets by induction from the local reducibility hypothesis `hloc`, then applying `pointedGluing_lower_bound_lemma`. The construction is intricate and involves the Baire space structure.

2. **`minFun_is_minimum`** (Proposition — Minimum Functions — line 113): This requires strong induction on ordinals α < ω₁, using `pointedGluing_lower_bound` at each step along with CB-rank analysis. It depends on `pointedGluing_lower_bound` being proved first.

### Files modified/created
- `RequestProject/PointedGluing/MinFun.lean` — proved `pointedGluing_lower_bound_lemma`, 2 sorries remain
- `RequestProject/PointedGluing/MinFunHelpers.lean` — new file with 5 fully proved helper lemmas

The project builds successfully with these changes.

# Summary of changes for run 094152e9-bc3a-4c17-afc6-be73b4811790
## Summary

Successfully resolved the `sorry` in `maxFun_is_maximum` (Proposition 3.9 — Maximum functions).

### What was done

The theorem `maxFun_is_maximum` states that for all ordinals α < ω₁:
1. `MaxFun α` is the maximum of all scattered functions with CB-rank ≤ α
2. `SuccMaxFun α` is the maximum for simple functions with CB-rank ≤ α+1

The proof was structured as a strong induction on α, with the key missing piece being `cbrank_eq_case` — handling the case when `CBRank f = α`.

### Proof structure

The proof of `cbrank_eq_case` follows the paper's outline:
1. **Local simplicity**: Use `decomposition_lemma_baire` to show that each point has a clopen neighborhood on which `f` is simple.
2. **Each piece reduces to MaxFun α**: Each simple piece has CB-rank β+1 ≤ α (so β < α), and by the induction hypothesis (item 2 at β), it reduces to `SuccMaxFun β ≤ MaxFun α`.
3. **Combine globally**: Use Lindelöf + disjointing to get a countable clopen partition, then combine all pieces via a gluing argument and self-similarity.

### New files and lemmas

**`RequestProject/PointedGluing/ClopenPartitionReduces.lean`** (new file):
- `ContinuouslyReduces.restrict_subtype` — ContinuouslyReduces is preserved under restriction to subtypes
- `ContinuouslyReduces.restrict_of_subset` — restriction to D ⊆ C preserves reductions
- `clopen_partition_to_gluing_reduces` — if each piece of a clopen partition reduces to Subtype.val on B, then f reduces to Subtype.val on GluingSet(fun _ => B)
- `locally_reduces_to_maxfun_implies_reduces` — local reducibility to MaxFun α implies global reducibility
- `subtypeInterHomeo` — homeomorphism between {a ∈ A | a.val ∈ U} and A ∩ U
- `subtype_inter_fun_eq` — equation relating f ∘ Subtype.val and the transferred function

**`RequestProject/PointedGluing/MaxFunMaximum.lean`** (modified):
- Added `simple_piece_reduces_to_maxfun` — transfers SimpleFun data via homeomorphism and applies `simple_reduces_to_MaxFun`
- Filled in `cbrank_eq_case` using the helpers above

**`RequestProject/PointedGluing/Theorems.lean`** (modified):
- Replaced `sorry` in `maxFun_is_maximum` with `exact maxFun_is_maximum' α hα`
- Fixed a pre-existing duplicate declaration of `pointedGluing_scattered`
- Removed a stray `end` keyword

### Verification

Both `maxFun_is_maximum` and `maxFun_is_maximum'` are fully proved with only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No sorry remains in `MaxFunMaximum.lean` or `ClopenPartitionReduces.lean`.

# Summary of changes for run 3b722add-04e8-4104-b20e-4b699522aa9f
## Summary of Progress on `maxFun_is_maximum`

### What was accomplished

The original sorry in `maxFun_item1_from_ih'` (in `RequestProject/PointedGluing/MaxFunMaximum.lean`) has been **resolved** — the file now contains zero sorries. The proof structure is complete:

- **`maxFun_item1_from_ih'`** (Item 1 of Proposition 3.9): Fully proved via two cases:
  - **CBRank f < α**: Uses the induction hypothesis directly, composing with `MaxFun_monotone`.
  - **CBRank f = α**: Delegates to `cbrank_eq_case` (in the new file `SelfSimilarity.lean`).

- **`maxFun_is_maximum'`** (the full Proposition 3.9): Proved by strong induction, combining Items 1 and 2.

### New file created: `RequestProject/PointedGluing/SelfSimilarity.lean`

This file contains the self-similarity infrastructure needed for combining local reductions:

1. **`gluingSet_flatten_const`** — ✅ Proved. Shows that `GluingSet(fun _ => GluingSet(fun _ => S)) ≤ GluingSet(fun _ => S)` via Cantor pairing/unpairing of indices.

2. **`gluingSet_copies_reduces_to_MaxFun_succ`** — ✅ Proved. Self-similarity for successor ordinals, using `gluingSet_flatten_const` and `MaxDom_succ`.

3. **`gluingSet_MaxDom_limit_inner_mem`** — ✅ Proved. Helper extracting the inner block structure of elements for limit ordinals.

4. **`mem_MaxDom_limit_prepend`** — ✅ Proved. Helper for membership in MaxDom at limit ordinals.

5. **`gluingSet_copies_reduces_to_MaxFun`** — ❌ **One sorry remains.** This is the full self-similarity lemma: `GluingSet(fun _ => MaxDom α) ≤ MaxFun α`. The base case (α = 0) and successor case are proved. The limit ordinal case requires constructing piecewise-continuous σ and τ functions using the induction hypothesis at each `enumBelow α j`, which involves intricate type-level plumbing.

6. **`cbrank_eq_case`** — ✅ Proved (depends on 5).

### Remaining sorry

**One sorry** remains in `SelfSimilarity.lean` at line 83: the limit case of `gluingSet_copies_reduces_to_MaxFun`. This is a pure topological/combinatorial statement about Baire space operations. The proof strategy is clear (transfinite induction with the IH providing σ_j, τ_j for each inner block, then pasting on clopen partitions), but the Lean formalization of the piecewise continuity argument proved resistant to automation.

### Relationship to Theorems.lean

The `maxFun_is_maximum` theorem in `Theorems.lean` still has its original sorry, because `MaxFunMaximum.lean` imports `Theorems.lean` (creating a circular dependency). A comment in `Theorems.lean` explains that the proof is available as `maxFun_is_maximum'` in `MaxFunMaximum.lean`. To resolve this, one could break the circular dependency by refactoring imports.

# Summary of changes for run 231f6148-a950-44fa-a91b-27264c173fd5
## Summary

I made significant progress on proving `maxFun_is_maximum` (Proposition 3.9), resolving the vast majority of the proof structure. The proof lives in `RequestProject/PointedGluing/MaxFunMaximum.lean`.

### What was accomplished

The theorem `maxFun_is_maximum'` in `MaxFunMaximum.lean` has the same type as `maxFun_is_maximum` and is structured as a strong induction proving both items simultaneously:

**Item 2** (SuccMaxFun α is maximum for simple functions) is **fully proved** via `maxFun_item2_from_item1'`, using:
- `ray_reduces_to_maxFun`: each ray of a simple function reduces to MaxFun α
- `ray_to_sub_gluing`: rays embed into the sub-gluing structure needed by `pointedGluing_upper_bound`
- `pointedGluing_upper_bound` with I = singleton sets, C = D = MaxDom α, g = id
- `PointedGluingFun_id` to convert from the pointed gluing form to SuccMaxFun α

**Item 1** (MaxFun α is maximum for CB ≤ α) is proved via `maxFun_item1_from_ih'`, which handles two cases:
- **CBRank f < α**: Uses the induction hypothesis (ih1) at the smaller ordinal CBRank f, then composes with `MaxFun_monotone`. **Fully proved.**
- **CBRank f = α**: Requires the decomposition lemma + combining step. **One sorry remains here.**

### Helper lemmas proved (all verified clean, no sorryAx)

1. `CBLevel_homeomorph` — CBLevel is invariant under homeomorphisms
2. `ray_reduces_to_maxFun` — Each ray of a simple function reduces to MaxFun α
3. `scatteredFun_of_CBLevel_empty` — ScatteredFun follows from finite CB level
4. `ray_to_sub_gluing` — Rays embed into sub-gluing structure
5. `maxFun_item2_from_item1'` — Item 2 from Item 1 (fully proved)
6. `simple_reduces_to_MaxFun` — Simple function with CB rank < α reduces to MaxFun α
7. `isEmpty_of_CBLevel_zero_empty` — Empty domain from CBLevel 0 = ∅
8. `continuouslyReduces_of_empty` — ContinuouslyReduces from empty type

### Remaining sorry (1 total in `MaxFunMaximum.lean`, line ~308)

The sorry is in `maxFun_item1_from_ih'`, specifically the case `CBRank f = α`. This requires:
1. Using `decomposition_lemma_baire` to get a clopen cover where f is locally simple
2. Refining to a disjoint cover via `baire_open_reduction_rel`
3. Extending f to `Baire → Baire` (since `gluingFun_upper_bound_backward` requires a total function)
4. Applying `gluingFun_upper_bound_backward` to combine the reductions
5. Embedding `GluingSet(fun _ => MaxDom α)` back into `MaxDom α`

This is a complex "continuous pasting" argument involving type-level plumbing between subtype functions and total functions on Baire space.

### Note on `maxFun_is_maximum` in `Theorems.lean`

The original sorry in `Theorems.lean` remains. Once the final sorry in `MaxFunMaximum.lean` is resolved, `maxFun_is_maximum` can be proved by `exact maxFun_is_maximum' α hα` (after importing MaxFunMaximum).

# Summary of changes for run 5633a014-3dbf-42f5-9a96-3ad1bfa3b051
## Summary

I made significant progress on proving `maxFun_is_maximum` (Proposition 3.9) but was unable to fully resolve the sorry due to the extreme complexity of this theorem. Here's what was accomplished:

### Architecture
Due to a circular dependency between `Theorems.lean` and `MaxMinhelpers.lean`, the proof was developed in a new file `RequestProject/PointedGluing/MaxFunMaximum.lean` that can import both.

### Proof Structure
The theorem `maxFun_is_maximum'` in `MaxFunMaximum.lean` establishes the correct induction skeleton:
- **Strong induction on α** proving both items simultaneously
- **Item 1** (MaxFun α is maximum for CB ≤ α) is reduced to `maxFun_item1_from_ih'`
- **Item 2** (SuccMaxFun α is maximum for simple functions) is reduced to `maxFun_item2_from_item1'`
- The induction correctly threads the hypotheses between items

### Helper Lemma: `ray_reduces_to_maxFun`
This key lemma (needed for Item 2) was mostly proved. It shows that each ray of a simple function reduces to MaxFun α by:
1. Reformulating the ray function on a flat subset A' ⊆ ℕ → ℕ (avoiding nested subtypes)
2. Proving continuity of the reformulated function
3. Proving scatteredness via `scattered_restrict`
4. Converting the ContinuouslyReduces back through the embedding

**One sorry remains**: showing `CBLevel f' γ = ∅` for γ ≥ α. This requires transferring the CB-rank bound across the subtype isomorphism between `{a : A | f a ∈ RaySet ...}` and `A'`.

### Remaining Sorries (3 total in `MaxFunMaximum.lean`)
1. **Line 78**: CBLevel empty condition in `ray_reduces_to_maxFun` (type coercion issue)
2. **Line 95**: `maxFun_item2_from_item1'` — requires invoking `pointedGluing_upper_bound` with specific parameters
3. **Line 113**: `maxFun_item1_from_ih'` — requires decomposition lemma + clopen partition combining

The original `Theorems.lean` retains `maxFun_is_maximum` with a sorry and a reference to the partial proof in `MaxFunMaximum.lean`.

### Why this is hard
This theorem involves:
- Transfinite strong induction on ordinals
- Complex subtype conversions (subtypes of subtypes of ℕ → ℕ)  
- The decomposition lemma (locally simple → globally reducible)
- Combining clopen partition reductions via `gluingFun_upper_bound_backward` (which expects `f : Baire → Baire`, not `f : A → Baire`)
- Type-level plumbing throughout that makes automation very difficult

# Summary of changes for run 00a36f1b-d845-4442-9deb-030e8778832a
## Progress on `pointedGluing_upper_bound` and `maxFun_is_maximum`

### `pointedGluing_upper_bound` (Proposition 3.5)

**Previous state**: 2 sorry's remained (lines 948 and 951) in the continuity-of-τ proof for the non-zeroStream case.

**Current state**: Reduced to 1 sorry (line 1025 in `Theorems.lean`).

**What was done**:
- Added a new helper lemma `continuousWithinAt_tau_at_block'` in `ContinuousOnTau.lean` — a weaker variant of `continuousWithinAt_tau_at_block` that only requires `ContinuousWithinAt` (not full `ContinuousOn`) of the replacement function at the target point.
- Restructured the non-zeroStream continuity proof to use `ContinuousWithinAt.comp` with three sub-goals:
  1. **ContinuousAt of pointedToGluing at z** (fully proved): Uses `continuousAt_congr` to reduce to continuity of `prepend i ∘ stripZerosOne i` on the open block.
  2. **MapsTo pointedToGluing (S ∩ block_i) R'** (mostly proved): Shows that pointedToGluing maps elements of the range ∩ block into the range where τ_j is ContinuousOn. The proof unfolds GluingFunVal, uses `hfJ : findJ i = rayIdx a ha_ne` to transport across dependent types, and establishes the structural equality. The remaining sorry is a technical value equality after `simp` unfolding — both sides compute to `prepend i (g i ⟨..., proof⟩).val` where the proofs differ by proof irrelevance but the `simp` chain doesn't quite resolve the final step.
  3. **ContinuousWithinAt.comp composition** (proved assuming MapsTo).

**Remaining sorry**: A single equality after GluingFunVal unfolding and simp rewrites, likely resolvable with more careful tactic work on dependent types (e.g., using `Eq.rec` or manual transport).

### `maxFun_is_maximum` (Proposition 3.9)

**Status**: Unchanged — remains as `sorry`.

This theorem requires transfinite induction using `decomposition_lemma_baire` (from `PrelimMemo/Scattered.lean`), which itself has multiple unresolved sorry's. Without the decomposition lemma, `maxFun_is_maximum` cannot be fully resolved.

### Files Modified
- `RequestProject/PointedGluing/Theorems.lean` — restructured the non-zeroStream case of τ continuity, reducing 2 sorry's to 1
- `RequestProject/PointedGluing/ContinuousOnTau.lean` — added `continuousWithinAt_tau_at_block'` helper lemma

All files build successfully.

# Summary of changes for run a3856d0c-fbe5-4250-962a-6ea296d3f8ec
## Summary of Progress

### `pointedGluing_upper_bound` (Proposition 3.5)

**Resolved the sequential convergence sorry** (originally at line 838): The proof that σ(x_n) → zeroStream when f(x_n) → y is now complete. This required:
1. Creating `RequestProject/PointedGluing/UpperBoundHelpers.lean` with 5 fully proved helper lemmas:
   - `rayIdx_tendsto_atTop_of_converge`: ray indices → ∞ when values converge to the base point
   - `disjoint_finset_member_tendsto_atTop`: elements from pairwise disjoint finsets grow when indices grow
   - `prependZerosOne_tendsto_zeroStream`: prependZerosOne with growing prefix converges to zeroStream
   - `disjoint_finset_idx_tendsto_of_member_tendsto`: reverse direction of the above
   - `finite_indices_with_small_members`: finiteness of indices with bounded members

**Resolved the zeroStream case of ContinuousOn τ**: Created `RequestProject/PointedGluing/ContinuousOnTau.lean` with 4 fully proved helper lemmas:
   - `firstNonzero_tendsto_of_converge_zeroStream`: first nonzero index → ∞ when converging to zeroStream
   - `rayLike_tendsto_of_idx_tendsto`: values agreeing with target on growing prefixes converge
   - `continuousWithinAt_tau_at_zeroStream`: continuity of τ at zeroStream using the filter argument
   - `continuousWithinAt_tau_at_block`: continuity of τ at non-zero points via local agreement

**Restructured the equation proof**: Duplicated the equation `f = τ ∘ PGF ∘ σ` as a local `have heq_main` inside the ContinuousOn τ goal, enabling its use for the zeroStream continuity argument.

**Remaining sorry** (2 small sub-sorries in the non-zeroStream block case, lines 948 and 951): These require showing that on each block, the composition `τ_j(findJ i) ∘ pointedToGluing` is ContinuousWithinAt and agrees with τ locally. The proof skeleton is set up with the block structure, `firstNonzero` equivalence, and the `h_tau_eq_on_block` lemma. The sub-sorries are focused on the composition continuity and the local congr condition.

### `maxFun_is_maximum` (Proposition 3.9)

This theorem requires a complex transfinite induction that depends on `decomposition_lemma_baire` (which is itself sorry'd in `PrelimMemo/Scattered.lean`), making it impossible to fully resolve without first proving that dependency. The theorem remains as `sorry`.

### Files Modified/Created
- `RequestProject/PointedGluing/UpperBoundHelpers.lean` — **new**, 5 sorry-free helper lemmas
- `RequestProject/PointedGluing/ContinuousOnTau.lean` — **new**, 4 sorry-free helper lemmas  
- `RequestProject/PointedGluing/Theorems.lean` — modified with partial progress on `pointedGluing_upper_bound`

All files build successfully with sorry warnings for the remaining unresolved statements.

# Summary of changes for run 0985e61a-cdd3-42db-8f15-cd597401551a
## Summary of work done

### `pointedGluing_upper_bound` (Proposition 3.5)
Significant progress was made on this theorem. The proof skeleton was fully set up (~200 lines) and several key challenges were resolved:

1. **Fixed pre-existing compilation errors** in the original proof:
   - Dependent type equality issues in `toPointed_pgluing` (resolved using `grind +splitImp`)
   - Dependent type equality in `hσ_eq_on_Oj` (resolved using `convert rfl` + `rayIdx_on_ray`)
   - `ContinuousOn.congr` direction mismatch (fixed)
   - `unfold_let τ` invalid tactic (replaced with `show` + explicit term)

2. **Proved ContinuousOn σ on each ray** (the composition toPointed j ∘ σ_j j is continuous)

3. **Proved the equation** f(a) = τ(PointedGluingFun(σ(a))) (both cases: f(a)=y and f(a)≠y)

4. **Two sorry holes remain** (lines 838 and 843):
   - Sequential convergence to zeroStream (σ(x_n) → zeroStream when f(x_n) → y)  
   - ContinuousOn τ on the range

### `maxFun_is_maximum` (Proposition 3.9)
- **Fixed the statement**: Changed `α < β` to `α ≤ β` in the CB-level condition (the original was off-by-one: it required CB rank ≤ α+1 instead of ≤ α, which made the theorem false for α=0)
- The proof body remains as `sorry` — this requires a complex transfinite induction that could not be completed in this session

### Other changes
- The file `RequestProject/PointedGluing/Theorems.lean` builds successfully with sorry warnings
- The dependent module `MaxMinhelpers.lean` also builds successfully
- No other files were modified

# Summary of changes for run f20efca7-8007-47aa-8229-ed6cd435ac57
Successfully resolved all `sorry`s in `RequestProject/PointedGluing/MaxMinhelpers.lean`. Here's what was done:

## Bug fix in `RequestProject/PointedGluing/Defs.lean`
The original `enumBelow` definition used `Classical.arbitrary` to pick an arbitrary function `ℕ → Iio α`, which didn't guarantee surjectivity. This made the monotonicity proofs impossible for limit ordinals, since the blocks of `MaxDom`/`MinDom` at limits might not cover all ordinals below the limit.

**Fix:** Modified `enumBelow` to prioritize a surjective enumeration when one exists (using `∃ f : ℕ → Iio α, Function.Surjective f`), falling back to the original behavior otherwise. Added `enumBelow_surj` proving surjectivity for ordinals `α < ω₁`. This preserves all existing proofs (they only used `enumBelow_lt`, which still holds).

## Proofs added to `MaxMinhelpers.lean`

Four helper lemmas were introduced and proved:

1. **`gluingSet_block_reduces`**: The n-th block of a `GluingSet` reduces to the whole, via `σ: x ↦ prepend n x` and `τ: y ↦ unprepend y`.

2. **`pointedGluingSet_block_reduces`**: A set `A` reduces to `PointedGluingSet(fun _ => A)`, via `σ: x ↦ prependZerosOne n x` and `τ: y ↦ stripZerosOne n y`.

3. **`MaxFun_reduces_succ`** / **`MinFun_reduces_succ`**: `MaxFun γ ≤ MaxFun (succ γ)` and `MinFun γ ≤ MinFun (succ γ)`, composing the block embedding lemmas with the successor unfolding.

4. **`MaxFun_block_reduces_limit`** / **`MinFun_block_reduces_limit`**: Each block of the limit construction reduces to the whole.

The main theorems `MaxFun_monotone` and `MinFun_monotone` are then proved by strong induction on β using `Ordinal.limitRecOn`:
- **Base case (β = 0):** α = 0, so reflexivity.
- **Successor case (β = succ γ):** By IH, `MaxFun α ≤ MaxFun γ`, then compose with `MaxFun_reduces_succ`.
- **Limit case:** Use `enumBelow_surj` to find a block n with `α ≤ enumBelow β n`, apply IH, then compose with `block_reduces_limit`.

All proofs are verified clean — no `sorry`, no non-standard axioms. The full project builds successfully.

# Summary of changes for run a40225e2-e3dc-4b40-baa8-159c693ace75
## Summary of Changes

### MaxMinhelpers.lean (`RequestProject/PointedGluing/MaxMinhelpers.lean`)

**Resolved 5 out of 6 sorries** (the original 3 sorries plus 3 new helper lemmas):

1. **`maxfun_is_scatter_leq_α`** ✅ — Proved that `MaxFun α` (the maximum function at CB-rank α) is scattered with CB-rank ≤ α. The proof uses transfinite induction on α with the `Ordinal.induction` principle, leveraging helper lemmas for the GluingSet and PointedGluingSet operations.

2. **`minfun_is_scatter_leq_succ_α`** ✅ — Proved that `MinFun α` (the minimum function at CB-rank α+1) is scattered with CB-rank ≤ α+1. The proof similarly uses transfinite induction, analyzing the base case (singleton), successor case, and limit case of the `MinDom` definition.

3. **`MaxFun_monotone`** ❌ — Remains as sorry. This lemma requires `maxFun_is_maximum` (from `Theorems.lean`), which states that `MaxFun α` is the maximum element in the class of functions with CB-rank ≤ α. Since `maxFun_is_maximum` is itself unproved, `MaxFun_monotone` cannot be resolved without it.

**New helper lemmas proved** (added to support the main proofs):
- `PointedGluingFun_id` — Shows that `PointedGluingFun` with identity functions equals `Subtype.val`
- `gluingSet_subtype_val_scattered` — `Subtype.val` on `GluingSet` is scattered if each block is scattered
- `gluingSet_CBLevel_empty` — CBLevel of `Subtype.val` on `GluingSet` is empty if each block's CBLevel is empty
- `MaxDom_zero`, `MaxDom_succ`, `MaxDom_limit` — Unfolding lemmas for the `MaxDom` definition
- `MinDom_zero`, `MinDom_succ`, `MinDom_limit` — Unfolding lemmas for the `MinDom` definition
- `CBLevel_pointedGluing_le` — CBLevel of pointed gluing at β is ⊆ {0^ω} when block CB-ranks ≤ β
- `CBLevel_succ_empty_of_subset_singleton` — If CBLevel β ⊆ {x}, then CBLevel (succ β) = ∅
- `pointedGluingSet_subtype_val_scattered` — `Subtype.val` on `PointedGluingSet` is scattered
- `pointedGluingSet_subtype_val_CBLevel_empty` — CBLevel empties above the block CB-ranks for pointed gluings

**Additional change**: Added imports for `CBRankHelpers`, `CBLevelOpenRestrict`, `CBRankSimpleHelpers`, and `Theorems` to access the existing CB-rank analysis infrastructure.

### Theorems.lean (`RequestProject/PointedGluing/Theorems.lean`)

**Fixed a syntax error** in the `maxFun_is_maximum` theorem statement (line 831): replaced malformed binder syntax `(hf : Continuous f) ScatteredFun f →` with proper `(_hf : Continuous f) (_hscat : ScatteredFun f) (_hcb : ...)`, and `(∀ β : omega1, ...)` with `(∀ β : Ordinal.{0}, ...)`.

**All 10 sorries remain unresolved**. These are the main theorems of the memoir (Propositions 3.5, 3.8, 3.9, 3.10, 3.11, 3.12, Theorems 3.13, 3.14, and Proposition 3.15), each requiring extensive construction proofs involving pointed gluing upper/lower bounds, transfinite induction with decomposition lemmas, and deep structural arguments about continuous reducibility. These theorems form an interdependent hierarchy and each would require hundreds of lines of formal proof.

Both files compile successfully with no errors (only sorry warnings and some unused variable warnings).

# Summary of changes for run 12d05ffb-fc56-45b7-ad60-a3fb6a85f0c8
## Summary of completed work

### 1. Resolved all sorries in section ReductionAndCB (`RequestProject/PrelimMemo/Scattered.lean`)

**`local_cb_derivative`** — Proved that for an open set U, the CB levels of the restricted function `f ∘ Subtype.val` on U equal `CBLevel f α ∩ U` (as images under `Subtype.val`). The proof proceeds by transfinite induction on α. The omega1 hypothesis was removed since it was unnecessary — the proof works for all ordinals.

**`limit_locally_lower`** — Proved that when the CB rank is a limit ordinal, every point has an open neighborhood where the CB rank of the restriction is strictly lower. This was decomposed into several helper lemmas:
- `exit_ordinal_not_limit`: The exit ordinal of any point cannot be a limit ordinal
- `exit_ordinal_is_successor`: The exit ordinal is always a successor
- `isolatedLocus_clears_succ_level`: Points in the isolated locus have neighborhoods clearing the next CB level
- `cbrank_restriction_le_of_empty_level`: Empty CB level in an open set bounds the rank of the restriction

### 2. Formalized Proposition 0dimanddisjointunion from `2_prelim_memo.tex`

Added the following definitions and theorems:

- **`IsLocallyInClass`** — A function f is locally in class F if every point has a clopen neighborhood where the restriction belongs to F
- **`IsDisjointUnion'`** — A function f is a disjoint union of functions (fᵢ) over a clopen partition (locally defined to avoid circular import with Gluing.lean)
- **`disjoint_union_implies_locally`** (backward direction) — Proved: if f is a disjoint union of F-functions, then f is locally in F
- **`locally_implies_disjoint_union_baire`** (forward direction) — Proved: if f is locally in F on a subspace of Baire, then f is a disjoint union of F-functions (with the natural hypothesis that F is closed under restriction to clopen subsets, matching the implicit assumption in the original paper)

### 3. Proved `decomposition_lemma_baire`

**Statement correction**: The original statement quantified over `∀ x : Baire`, which is incorrect when `x ∉ A` (the restricted domain may be empty, making `SimpleFun` false). The corrected version quantifies over `∀ x : A`. The original incorrect statement is preserved as a commented-out block.

**Proof approach**: Instead of the paper's ordinal induction proof, a direct construction was used:
1. For each point x : A, the CB hierarchy gives a successor exit ordinal β where x leaves
2. The isolated locus provides an open neighborhood where f is constant on CBLevel f β
3. This neighborhood is refined to a Baire-clopen set
4. The restriction to this clopen set is shown to be simple

Key helper lemmas proved:
- `cb_stabilizing_set_nonempty`: The set of ordinals where CB levels stabilize is nonempty
- `cbLevel_at_cbRank_empty`: The CB level at the CB rank is empty for scattered functions
- `scattered_restriction_open`: Restrictions of scattered functions to open sets are scattered
- `isolatedLocus_gives_simple_neighborhood`: The isolated locus provides neighborhoods with both constancy and level-clearing
- `restriction_to_clopen_is_simple`: The key lemma connecting all ingredients to SimpleFun

All proofs use only standard axioms (propext, Classical.choice, Quot.sound) — verified via `#print axioms`.

### Pre-existing issues not addressed
- `sierpinski_rat_homeomorph` (sorry, not requested)
- `first_reduction_theorem` (sorry, not requested)  
- `exists_clopen_subset_of_open` for general metrizable spaces (sorry, not requested — the Baire-specific version `baire_exists_clopen_subset_of_open` is proved)
- Pre-existing syntax error in `RequestProject/PointedGluing/Theorems.lean` (line 831)

# Summary of changes for run e020f2c4-7fbe-45c4-bcb5-eedc36c24cac
All `sorry`s in `theorem baire_open_reduction_rel` in `RequestProject/PrelimMemo/blackboard.lean` have been resolved. The proof is fully formalized and compiles successfully, depending only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Proof structure:**

The theorem proves the *open reduction property* for subspaces of the Baire space: given a countable family of open sets `U n` in a subspace `A ⊆ ℕ → ℕ`, there exists a pairwise-disjoint family of open sets `V n` with `V n ⊆ U n` and `⋃ V n = ⋃ U n`.

The proof proceeds through several helper lemmas building up the necessary infrastructure:

1. **`baire_fiber_isClopen`** — The set `{f | f i = a}` is clopen in the Baire space (preimage of a clopen singleton under a continuous projection).

2. **`baire_cylinder_isClopen`** — Cylinder sets (finite intersections of fibers) are clopen, proved by induction on the finset.

3. **`nat_singleton_basis`** — Singletons form a topological basis for ℕ (discrete topology).

4. **`baire_has_clopen_basis`** — The Baire space has a countable topological basis consisting of clopen cylinder sets.

5. **`baire_open_eq_countable_union_clopen`** — Every open set in the Baire space is a countable union of clopen sets (using the clopen basis).

6. **`subspace_open_eq_countable_union_clopen`** — The same holds in any subspace of the Baire space (traces of clopen sets are clopen in the subspace).

7. **`disjointed_clopen`** — The `disjointed` operation preserves clopen-ness (since `disjointed f n = f n \ finite_union`, and clopen sets are closed under finite unions and differences).

The main theorem then:
- Decomposes each `U n` into clopen sets `C n k`
- Flattens to a single sequence via `Nat.pair`/`Nat.unpair`
- Applies `disjointed` to get pairwise-disjoint clopen pieces
- Reassembles by grouping pieces back by their original index `n`
- Verifies openness (union of clopen sets), subset inclusion, disjointness (from `disjoint_disjointed`), and union preservation (from `iUnion_disjointed`).

# Summary of changes for run 96c4e0d3-d2b4-4a7d-96a9-fe1bc29f0bf1
I completed all three requested tasks:

## 1. Resolved the `sorry` in `CBrank_regular_simple` (Proposition 3.8)

In `RequestProject/PointedGluing/Theorems.lean`, the theorem `CBrank_regular_simple` had a `sorry` in the limit ordinal case of the regularity proof. The case had hypotheses `hlim : Order.IsSuccLimit α` (α is a limit ordinal) and `h_succ : ∃ γ, α = Order.succ γ` (α is a successor ordinal), which are contradictory. I closed this case with:
```lean
obtain ⟨γ, hγ⟩ := h_succ
exact absurd hγ.symm (Order.IsSuccLimit.succ_ne hlim γ)
```
The proof now compiles with only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## 2. Formalized `Def_MinMaxFunc` (Definition 3.5 from the memoir)

In `RequestProject/PointedGluing/Defs.lean`, I added the following definitions corresponding to Definition 3.5 in `3_general_struct_memo.tex`:

- **`enumBelow α`** — an arbitrary ℕ-indexed enumeration of ordinals below α (used for the limit case of `MaxDom`)
- **`cofinalSeq α`** — an arbitrary cofinal sequence in a limit ordinal α (used for the limit case of `MinDom`)
- **`MaxDom α`** — domain of the maximum function ℓ_α, defined by transfinite induction using `Ordinal.limitRecOn`:
  - Base: `MaxDom 0 = ∅`
  - Successor: `MaxDom (β+1) = GluingSet (fun _ => PointedGluingSet (fun _ => MaxDom β))` (i.e., ω·pgl(ℓ_β))
  - Limit: `MaxDom α = GluingSet (fun n => MaxDom (enumBelow α n))` (i.e., ⊔_n ℓ_{β_n})
- **`MinDom α`** — domain of the minimum function k_{α+1}, similarly defined:
  - Base: `MinDom 0 = PointedGluingSet (fun _ => ∅)` (i.e., k_1 = pgl(∅))
  - Successor: `MinDom (β+1) = PointedGluingSet (fun _ => MinDom β)` (i.e., pgl(k_{β+1}))
  - Limit: `MinDom α = PointedGluingSet (fun n => MinDom (cofinalSeq α n))`
- **`MaxFun α`** and **`MinFun α`** — the identity functions on their respective domains (Subtype.val), as noted in the memoir.

## 3. Adapted the statement of `maxFun_is_maximum` (Proposition 3.9)

The old existential statement was renamed to `maxFun_is_maximum_exists` and preserved for reference. The new `maxFun_is_maximum` directly references the concrete `MaxFun α` definition:
```lean
theorem maxFun_is_maximum (α : Ordinal.{0}) (hα : α < omega1) :
    ScatteredFun (MaxFun α) ∧
    (∀ β, α < β → CBLevel (MaxFun α) β = ∅) ∧
    (∀ (X' Y' : Type) [TopologicalSpace X'] [TopologicalSpace Y'] (f : X' → Y'),
      ScatteredFun f → (∀ β, α < β → CBLevel f β = ∅) → ContinuouslyReduces f (MaxFun α))
```

All modified files (`Defs.lean` and `Theorems.lean`) build successfully.

# Summary of changes for run 11e57b99-2273-4a17-87d4-ecc00eb11fc8
## Summary of Work on `pointedGluing_upper_bound` and `CBrank_regular_simple`

### `CBrank_regular_simple` (Proposition 3.8) — Partially Resolved

**Progress made in this session:**
- Restructured the regularity proof in the `ray_cb m = α` case by adding an ordinal trichotomy (zero, successor, limit):
  - **α = 0 case**: Fully proved. Any `n > m` works since `ray_cb n ≥ 0`.
  - **α = γ + 1 (successor) case**: Fully proved. The cofinality property with `β = γ` yields `n > m` with `ray_cb n > γ`, hence `ray_cb n ≥ γ + 1 = α`.
  - **α is a limit ordinal case**: Remains as `sorry` (line 803).

**Analysis of the remaining sorry (limit ordinal case):**
The remaining case requires showing that when `ray_cb m = α` and `α` is a limit ordinal, there exists `n > m` with `ray_cb n = α`. This appears to be a subtle edge case in the paper's proof (Proposition 3.8 of the memoir). The paper establishes only the *cofinality* property (∀ β < α, ∀ m, ∃ n > m, ray_cb n > β), which implies regularity when `ray_cb m < α` but does not directly yield regularity when `ray_cb m = α` for a limit ordinal `α`. The scenario where one ray achieves the limit supremum while no later ray does appears mathematically consistent with the stated hypotheses, suggesting this may be a gap in the paper's argument. However, this edge case may not arise in the paper's actual applications (which primarily use successor ordinals).

### `pointedGluing_upper_bound` (Proposition 3.5) — Not Resolved

This theorem requires constructing an explicit continuous reduction (σ, τ) from `f` to the pointed gluing of `(g_i)`. The construction involves:
1. Translating between the `GluingSet` (prepend encoding) and `PointedGluingSet` (prependZerosOne encoding)
2. Gluing together individual ray reductions obtained from the `hpieces` hypothesis  
3. Proving continuity at the base point `0^ω` using `sufficient_cond_continuity`

The theorem's type signature involves deeply nested dependent types with conditionals (e.g., `if i ∈ I j then C i else ∅`), making both manual construction and automated proof search extremely difficult. Multiple attempts with different proof strategies were unsuccessful.

### Project State
- All files compile successfully with `lake build`
- The four helper files (`Defs.lean`, `CBRankHelpers.lean`, `CBLevelOpenRestrict.lean`, `CBRankSimpleHelpers.lean`) remain sorry-free
- The sorry at line 803 (limit ordinal case of `CBrank_regular_simple`) is the only remaining sorry attributable to the two target theorems; the other sorries (lines 839–1064) are for separate theorems not targeted in this task

# Summary of changes for run 9f58dcd8-e354-4ff5-acaa-4b6eac53af3a
## Summary of Progress

I made substantial progress on the two target theorems, though neither is fully resolved due to their deep mathematical complexity.

### `CBrank_regular_simple` (Proposition 3.8) — Partially Proved

**What was accomplished:**
- Added `Continuous f` and `y ∈ B` as hypotheses (the original statement was missing these, which are implicit in the paper's context of continuous functions in 𝒞). A docstring note explains this.
- Proved the **supremum result** (`⨆ n, ray_cb n = α`) completely, using a chain of helper lemmas.
- Proved **regularity** for the case `ray_cb m < α` (the generic case), using a cofinality argument.
- The **one remaining sorry** (line 774) is for an edge case where `ray_cb m = α` and `α` is a limit ordinal — the cofinality argument doesn't directly yield a later term achieving the exact value `α`. For successor ordinals, this case is handled.

**New helper files created (fully proved, no sorries):**
- `RequestProject/PointedGluing/CBLevelOpenRestrict.lean` — Key lemma: for open S ⊆ X, CBLevel of f|_S equals S ∩ CBLevel of f (the `CBLevel_open_restrict` iff). Also: scattered functions restrict to scattered functions, and the clopen union emptiness lemma.
- `RequestProject/PointedGluing/CBRankSimpleHelpers.lean` — Helper lemmas for the ray decomposition: RaySet is open, ray subtypes are open (for continuous f), every point is in a ray or maps to y, CBRank ≤ α for each ray, CBLevel is constant on rays ⟹ next level empty, supremum equals α, and the regularity contradiction lemma.

### `pointedGluing_upper_bound` (Proposition 3.5) — Not Proved

This theorem requires constructing an explicit continuous reduction (σ, τ) from f to the pointed gluing. The construction involves:
1. Translating between the `GluingSet` (prepend encoding) and `PointedGluingSet` (prependZerosOne encoding)
2. Gluing together individual ray reductions
3. Proving continuity at the base point using `sufficient_cond_continuity`

The construction is extremely detailed and type-theoretically intricate. The sorry remains at line 657.

### Project builds successfully
All files compile with `lake build`. The two new helper files (`CBLevelOpenRestrict.lean` and `CBRankSimpleHelpers.lean`) are completely sorry-free and contain 16 fully proved lemmas that form the mathematical infrastructure for the CB-level analysis of open restrictions and ray decompositions.

# Summary of changes for run 2fcd637b-3f8d-44ec-9dc7-4d5724a715ca
I resolved both theorems in the PointedGluing files:

## 1. `theorem emptyFun` (in `RequestProject/PointedGluing/Theorems.lean`)

The original `emtpyFun` was commented out because it was malformed (wrong case for `CBrank`, missing hypothesis name, invalid LaTeX `\emptyset` syntax). I wrote a corrected version:

```lean
theorem emptyFun (A B : Set (ℕ → ℕ)) (f : A → B)
    (hf : ScatteredFun (fun x : A => (f x : ℕ → ℕ)))
    (h : CBRank (fun x : A => (f x : ℕ → ℕ)) = 0) : A = ∅
```

Key changes from the original:
- `CBrank` → `CBRank` (correct capitalization)
- Added `ScatteredFun` hypothesis (the result is false without it — e.g., the identity on a perfect set has CBRank 0 but nonempty domain)
- Named the hypothesis `h`
- `\emptyset` → `∅`

The proof uses three helper lemmas:
- `CBLevel_zero_ne_succ_of_scattered_nonempty`: scattered functions on nonempty domains have nontrivial CB derivative
- `CBRank_stabilization_set_nonempty`: the stabilization set is nonempty for scattered functions
- `CBRank_pos_of_scattered_nonempty`: combining the above, CBRank > 0 for scattered functions on nonempty domains

## 2. `theorem CBrank_pointedGluing_regular` (in `RequestProject/PointedGluing/Theorems.lean`)

This is Proposition 3.2 from the memoir. I also fixed a syntax error in the statement (`h\alpha : \alpha>0` → `hαpos : α > 0`).

The proof required substantial infrastructure, which I placed in a new file `RequestProject/PointedGluing/CBRankHelpers.lean`. The key helper lemmas are:

- **Block correspondence lemmas**: `CBLevel_block_forward` and `CBLevel_block_backward` — these establish that the CB derivative of the pointed gluing on each block corresponds exactly to the CB derivative of the component function, proved by transfinite induction
- **`isolatedLocus_block_transfer`**: transfers isolation information between the block and the full pointed gluing
- **`CBLevel_block_empty_above_rank`**: blocks empty out once the CB rank of the component is exceeded
- **`CBLevel_pointedGluing_subset`**: only zeroStream survives at level α (the ⊆ direction)
- **`zeroStream_mem_CBLevel_le`**: zeroStream is in all CB levels up to α (the ⊇ direction)
- Various topology helpers: `blockSet_isOpen`, `prependZerosOne_eventually_in_nhds`, `exists_large_cbrank`, etc.

Both theorems compile without `sorry` and depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

# Summary of changes for run 1fbadabe-5348-4efd-8a0d-a8ccda7f5746
## Summary of Changes

I reviewed the project — a formalization of a research memoir on continuous reducibility between functions on the Baire space — checking proofs against the .tex files, adapting theorems, optimizing proofs, and filling sorries where possible.

### Build Fix
- **`RequestProject/PointedGluing/Theorems.lean`**: Fixed a build error caused by a malformed theorem statement `emtpyFun` (line 343). The statement used `CBrank` (wrong capitalization, should be `CBRank`), had a parenthesized hypothesis without a name `(CBrank f = 0)`, and referenced `A.is_empty` which is not valid Lean syntax. Commented it out with an explanation.

### Proof Optimizations (exact? cleanup)
- **`RequestProject/PrelimMemo/Gluing.lean`**: Replaced 4 `exact?` tactic calls with explicit proof terms:
  - `partitionIndex_locallyConstant P hclopen hdisj hcover` for IsLocallyConstant proof
  - `h_partitionIndex.continuous` for continuity from locally constant
  - `Continuous.subtype_mk h_cont _` for subtype continuity
  - Explicit IsClopen proof for `{z | z 0 = i}` using `isClosed_eq` and `isOpen_discrete`

### Sorry Elimination
- **`RequestProject/PrelimMemo/Scattered.lean`**: Proved the **splitting lemma** (`nlc_splitting_lemma`) — a key helper for the Cantor scheme construction. This lemma states that for a nowhere locally constant continuous function from a metric space to a T₂ space, any open ball contains two disjoint sub-balls whose images are separated by disjoint open sets. The proof was found to be a consequence of the already-proven `splitting_lemma_nlc` in the same file (with slightly different parameter ordering). This also eliminated the `exact?` that was serving as a sorry inside `cantor_scheme_exists`.

### What Remains
The project still contains ~60 sorry statements across 6 files. These are all deep, interdependent research-level results from the memoir:

- **IntroMemo.lean** (4 sorries): Main Theorems 1-3 (WQO results) and `scattered_imp_locallyConstantLocus_univ`
- **PrelimMemo/Scattered.lean** (3 sorries): Sierpiński's theorem, first reduction theorem, clopen basis lemma, decomposition lemma
- **PointedGluing/Theorems.lean** (12 sorries): CB-rank analysis, max/min functions, general structure theorem
- **CenteredMemo/Theorems.lean** (9 sorries): Centered function characterization, rigidity, BQO results
- **PreciseStructMemo/Theorems.lean** (21 sorries): Wedge operation, finite generation, precise structure theorem
- **DoubleSuccMemo/Theorems.lean** (11 sorries): Fine partitions, diagonal/vertical theorems, double successor induction

These are genuinely deep research-level results requiring transfinite induction over CB-rank levels, explicit constructions of continuous reductions, BQO/WQO theory, and intricate topological arguments that go well beyond what can be automated. The entire project builds successfully with these remaining sorries.

# Summary of changes for run 52b18c96-ba7d-47ae-8ef6-189b835d14b9
I was unable to eliminate additional `sorry` statements from `RequestProject/PointedGluing/Theorems.lean` beyond what the previous agent accomplished. The file still compiles successfully, but 12 `sorry` statements remain.

**What was accomplished:**
- I identified and fixed a bug in the statement of `CBrank_pointedGluing_regular` (Proposition 3.2): the original statement was **false** as formalized — a counterexample was found where all `cbranks` are 0, making `α = 0`, but `CBLevel f 0 = univ ≠ {0^ω}`. I added the hypothesis `(hα_pos : 0 < α)` to make the statement well-posed.

**Why the remaining 12 theorems could not be proved:**
These are deeply interdependent research-level results from a memoir on continuous reducibility between functions. They involve:
- Transfinite induction over Cantor–Bendixson rank levels (using `Ordinal.limitRecOn`, which is particularly hard to work with in formal proofs)
- Explicit constructions of continuous reductions (σ, τ pairs) with delicate continuity arguments
- Existence of maximum/minimum functions via recursive pointed gluing constructions
- Cross-level comparison theorems (the General Structure Theorem)
- WQO/BQO arguments combining all of the above

The remaining theorems and their key dependencies:
1. `CBrank_pointedGluing_regular` — CB rank analysis of pointed gluings (self-contained but deep)
2. `pointedGluing_upper_bound` — Proposition 3.5 (self-contained construction)
3. `CBrank_regular_simple` — Proposition 3.8 (self-contained CB analysis)
4. `maxFun_is_maximum` — Proposition 3.9 (depends on 1, 2, 3)
5. `minFun_is_minimum` — Proposition 3.12 (depends on 6, 7)
6. `pointedGluing_lower_bound_lemma` — Lemma 3.10 (self-contained construction)
7. `pointedGluing_lower_bound` — Proposition 3.11 (depends on 6)
8. `classification_compact_domains` — Theorem 3.13 (depends on 4, 5)
9. `general_structure_theorem` — Theorem 3.14 (depends on 10, 11)
10. `general_structure_limit` — Theorem 3.14 Item 1 (deep standalone result)
11. `general_structure_successor` — Theorem 3.14 Item 2 (depends on 4, 5)
12. `finitely_generated_implies_bqo` — Proposition 3.15 (depends on 9)

Multiple proof strategies were attempted for each theorem, including detailed informal proof sketches, decomposition into helper lemmas, and well-founded induction approaches. The complexity of the transfinite recursion definitions (particularly `CBLevel` via `Ordinal.limitRecOn`) and the intricate topological constructions proved too challenging for automated proof search.

# Summary of changes for run 233eb8a5-2465-4304-a2b4-a3f67dedf3bc
I was able to partially address the request. Out of 13 original `sorry` statements in `RequestProject/PointedGluing/Theorems.lean`, I eliminated 1:

**Proved:**
- `consequences_general_structure_1` (Corollary 3.16, Item 1) — proved by introducing and proving a new helper lemma `pointedGluing_scattered`, which shows that the pointed gluing of scattered functions is itself scattered. The corollary then follows by taking the witness `k` to be the pointed gluing function itself, with `ContinuouslyReduces.refl`.

**Still remaining (12 sorries):**
The remaining theorems are deep results from the research memoir on continuous reducibility between functions. Each requires extensive mathematical infrastructure (transfinite induction, detailed CB-rank analysis, construction of maximum/minimum functions, etc.) that proved beyond what could be completed within the available proof search budget:

1. `CBrank_pointedGluing_regular` — Proposition 3.2
2. `pointedGluing_upper_bound` — Proposition 3.5
3. `CBrank_regular_simple` — Proposition 3.8
4. `maxFun_is_maximum` — Proposition 3.9
5. `minFun_is_minimum` — Proposition 3.12
6. `pointedGluing_lower_bound_lemma` — Lemma 3.10
7. `pointedGluing_lower_bound` — Proposition 3.11
8. `classification_compact_domains` — Theorem 3.13
9. `general_structure_theorem` — Theorem 3.14
10. `general_structure_limit` — Theorem 3.14, Item 1
11. `general_structure_successor` — Theorem 3.14, Item 2
12. `finitely_generated_implies_bqo` — Proposition 3.15

These are genuinely deep research-level results. Many are interdependent (e.g., `classification_compact_domains` requires `maxFun_is_maximum` and `minFun_is_minimum`; `finitely_generated_implies_bqo` requires `general_structure_theorem`). The file compiles successfully with these sorries.

# Summary of changes for run 589c5c15-2b86-4a2c-8442-882cc5249c2f
I worked on removing `sorry` statements from `RequestProject/PointedGluing/Theorems.lean`. The file originally contained 14 `sorry` statements, all corresponding to deep mathematical theorems from a research memoir on continuous reducibility between functions.

**Successfully proved (1 main theorem + 8 helper lemmas):**

- **`pointedGluingFun_preserves_continuity`** — Fact 3.1: The pointed gluing operation preserves continuity. This was proved by decomposing it into 8 helper lemmas:
  1. `strip_mem_of_pointedGluingSet` — membership of stripped sequence in the appropriate set
  2. `pointedGluingFun_eq_on_block` — the function formula on non-zero elements
  3. `continuous_stripZerosOne` — continuity of the strip operation
  4. `isOpen_block` — openness of block sets in the product topology
  5. `firstNonzero_eq_of_block` — determining the first nonzero index
  6. `ne_zeroStream_of_block` — elements in blocks are not the zero stream
  7. `strip_mem_of_block` — membership proof for specific block index
  8. `continuous_block_restrict` — continuity of the restricted function on each block
  9. `continuousAt_pointedGluingFun_nonzero` — continuity at non-zero points

The main theorem proof combines continuity at the basepoint 0^ω (via the existing `zeroStream_continuity_point`) with the new `continuousAt_pointedGluingFun_nonzero` lemma.

**Remaining 13 sorry statements** are all major theorems from the memoir (Propositions 3.2, 3.5, 3.8, 3.9, 3.12, Lemma 3.10, Proposition 3.11, Theorems 3.13, 3.14 Items 1&2, Proposition 3.15, and Corollary 3.16 Item 1). These are deep, interdependent results requiring extensive mathematical infrastructure (transfinite CB-rank analysis, construction of explicit continuous reductions, BQO theory) that could not be resolved within the available budget. The file compiles cleanly with the remaining sorries.

# Summary of changes for run 0a0631b7-0fae-4d3c-beb8-695193b7ee51
Successfully removed all `sorry` instances from `RequestProject/PrelimMemo/Gluing.lean`. 

The file had 6 `sorry` instances, all concentrated in the `gluingFun_upper_bound_backward` theorem and its dependency `disjoint_union_reduces_gluing`. There was also a critical issue: stray `import` statements in the middle of the file (line 279) that prevented compilation.

**Changes made:**

1. **Removed stray imports** — Lines 279–282 contained `import Mathlib` and `import RequestProject.PrelimMemo.Gluing` (a circular self-import) in the middle of the file. These were removed.

2. **Removed `[TopologicalSpace Baire]`** — The theorem `gluingFun_upper_bound_backward` had an explicit `[TopologicalSpace Baire]` instance parameter that conflicted with the canonical product topology on `ℕ → ℕ`, preventing the use of existing lemmas like `continuous_prepend` and `continuous_unprepend`. This was removed since `Baire = ℕ → ℕ` already inherits the product topology.

3. **Proved `gluingFun_upper_bound_backward`** — Decomposed into a clean proof skeleton:
   - Used `continuous_pasting_on_clopen` (also proved in this session) to construct σ by pasting the per-piece reductions along the clopen partition.
   - Defined τ(z) = τ_i(z₀)(unprepend z) and proved continuity via `continuousOn_piecewise_clopen` (also proved).
   - Proved the equation `f(x) = τ(gl(σ(x)))` by chasing the definitions through `GluingFunVal_prepend` and `unprepend_prepend`.

4. **Proved `disjoint_union_reduces_gluing`** — The corollary now follows from the backward theorem.

5. **Added helper lemmas** (all proved, no sorry):
   - `continuous_pasting_on_clopen` — Pasting continuous functions on a clopen partition
   - `GluingFunVal_prepend` — Computing GluingFunVal at a prepend element  
   - `continuousOn_piecewise_clopen` — ContinuousOn for piecewise functions on clopen covers
   - `gluing_backward_eq` — The equation in the backward direction
   - `gluing_backward_tau_cont` — τ continuity in the backward direction

All proofs compile successfully with only standard axioms (propext, Classical.choice, Quot.sound).

# Summary of changes for run 6a4023a5-80eb-4ddc-a3b4-7c32b9cf09f2
## Summary of Changes

This project formalizes a research memoir on continuous reducibility between functions — a deep area of descriptive set theory. The project contains ~53 `sorry` statements representing the core theorems of this multi-chapter memoir, including results about well-quasi-orders, Cantor-Bendixson analysis, pointed gluings, centered functions, wedge operations, and the precise structure theorem.

### What was accomplished:

1. **`RequestProject/PrelimMemo/Gluing.lean`** — Fixed 4 incomplete proofs (`exact?` calls) in the locally constant function theory:
   - `locally_constant_infinite_image_forward`: Fixed the continuity proof for the restricted codomain map (used `continuous_of_discreteTopology` since ℕ has discrete topology)
   - `id_nat_reduces_locally_constant`: Fixed three proof goals:
     - Existence of countable dense subset (used `SeparableSpace.exists_countable_dense`)
     - Locally constant function has constant open neighborhoods (used `IsLocallyConstant.isOpen_fiber_`)
     - Continuity of σ : ℕ → X (used `continuous_of_discreteTopology`)
     - Continuity of restricted τ on discrete range (used `continuous_of_discreteTopology`)

2. **`RequestProject/IntroMemo.lean`** — Decomposed `scatteredIffEmptyKernel` into structured helper lemmas:
   - **`perfectKernel_eq_compl`** (fully proved): Shows the perfect kernel equals the complement of the locally constant locus, since the locally constant locus is open (hence its complement is the smallest closed set containing itself)
   - **`locallyConstantLocus_univ_imp_scattered`** (fully proved): The backward direction — if every point is locally constant, then f is scattered
   - **`scattered_imp_locallyConstantLocus_univ`** (sorry): The forward direction — if f is scattered, continuous, X metrizable, Y T₂, then every point is locally constant. This is the mathematically deep direction requiring careful use of metrizability and sequential arguments.
   - **`scatteredIffEmptyKernel`** (now uses the helpers): The main theorem now follows directly from the three helper lemmas above, with only the forward direction remaining as a sorry.

### What remains:

The vast majority of remaining `sorry` statements are deep results from the research memoir:
- **IntroMemo.lean**: Main Theorems 1-3 (WQO results), `scattered_imp_locallyConstantLocus_univ`
- **PrelimMemo/Scattered.lean**: Sierpiński's theorem, first reduction theorem, clopen basis lemma, decomposition lemma
- **PrelimMemo/Gluing.lean**: `gluingFun_upper_bound_backward`
- **PointedGluing/Theorems.lean**: 14 theorems about pointed gluings, CB-rank analysis, max/min functions, general structure theorem
- **CenteredMemo/Theorems.lean**: 9 theorems about centered functions, cocenters, rigidity
- **PreciseStructMemo/Theorems.lean**: 21 theorems about wedge operations, finite generation, precise structure theorem

These are genuinely deep research-level results that form the mathematical content of a multi-chapter memoir on continuous reducibility. Each requires substantial mathematical infrastructure and proof techniques (transfinite induction, Cantor-Bendixson analysis, BQO theory, etc.) that go beyond what can be automated.

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
