import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `3_general_struct_memo.tex` — Definitions

This file contains the definitions from Chapter 3 (Pointed Gluing and the General
Structure) of the memoir on continuous reducibility between functions.

## Main definitions

* `zeroStream` — the constant zero sequence `0^ω` in the Baire space
* `prependZerosOne` — prepend `i` zeros and a `1` to a sequence
* `stripZerosOne` — strip `i` zeros and a `1` from a sequence
* `PointedGluingSet` — pointed gluing of a sequence of subsets of the Baire space
* `PointedGluingFun` — pointed gluing of a sequence of functions on the Baire space
* `IsRegularOrdSeq` — a sequence of ordinals is regular
* `RaySet` — the n-th ray of a set at a point
* `IsReducibleByPieces` — a sequence of functions is reducible by finite pieces to another
* `SetsConvergeTo` — a sequence of sets converges to a point
-/

noncomputable section

/-!
## Baire space operations for pointed gluing
-/

/-- The constant zero sequence `0^ω ∈ ℕ → ℕ`. -/
def zeroStream : ℕ → ℕ := fun _ => 0

/-- Prepend `i` zeros followed by a `1` to a sequence `x : ℕ → ℕ`.
This produces the sequence `(0)^i ⌢ (1) ⌢ x`. -/
def prependZerosOne (i : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if k < i then 0
    else if k = i then 1
    else x (k - i - 1)

/-- Strip `i` zeros and a `1` from the front of a sequence.
Inverse of `prependZerosOne i` when the sequence starts with `(0)^i ⌢ (1)`. -/
def stripZerosOne (i : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => x (k + i + 1)

theorem stripZerosOne_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    stripZerosOne i (prependZerosOne i x) = x := by
  ext k; simp only [stripZerosOne, prependZerosOne]
  have h1 : ¬ (k + i + 1 < i) := by omega
  have h2 : ¬ (k + i + 1 = i) := by omega
  simp [h1, h2]
  congr 1; omega

theorem prependZerosOne_head_eq_zero (i : ℕ) (x : ℕ → ℕ) (k : ℕ) (hk : k < i) :
    prependZerosOne i x k = 0 := by
  simp [prependZerosOne, hk]

theorem prependZerosOne_at_i (i : ℕ) (x : ℕ → ℕ) :
    prependZerosOne i x i = 1 := by
  simp [prependZerosOne]

/-- A sequence starts with `i` zeros followed by a `1`. -/
def StartsWithZerosOne (i : ℕ) (x : ℕ → ℕ) : Prop :=
  (∀ k, k < i → x k = 0) ∧ x i = 1

theorem startsWithZerosOne_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    StartsWithZerosOne i (prependZerosOne i x) :=
  ⟨fun k hk => prependZerosOne_head_eq_zero i x k hk,
   prependZerosOne_at_i i x⟩

/-- `prependZerosOne i` is injective. -/
theorem prependZerosOne_injective (i : ℕ) : Injective (prependZerosOne i) := by
  intro x y h
  have := congr_arg (stripZerosOne i) h
  rwa [stripZerosOne_prependZerosOne, stripZerosOne_prependZerosOne] at this

/-!
## Pointed Gluing of Sets
-/

/-- The pointed gluing of a sequence `(F_i)_{i ∈ ℕ}` of subsets of the Baire space:
$$\mathrm{pgl}_{i \in \mathbb{N}} F_i = \{0^\omega\} \cup \bigcup_{i \in \mathbb{N}} (0)^i (1) F_i$$
-/
def PointedGluingSet (F : ℕ → Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {zeroStream} ∪ ⋃ i, prependZerosOne i '' (F i)

/-- `zeroStream` is always in the pointed gluing. -/
theorem zeroStream_mem_pointedGluingSet (F : ℕ → Set (ℕ → ℕ)) :
    zeroStream ∈ PointedGluingSet F :=
  Or.inl rfl

/-- If `x ∈ F i`, then `prependZerosOne i x ∈ PointedGluingSet F`. -/
theorem prependZerosOne_mem_pointedGluingSet (F : ℕ → Set (ℕ → ℕ)) (i : ℕ) (x : ℕ → ℕ)
    (hx : x ∈ F i) : prependZerosOne i x ∈ PointedGluingSet F :=
  Or.inr (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hx⟩)

/-!
## Pointed Gluing of Functions

We define the pointed gluing abstractly, specifying its behavior on the base point
`0^ω` and on each block `(0)^i(1) · A_i`.
-/

/-- The first index `k` where `x k ≠ 0`, if it exists. For sequences in the pointed
gluing (other than `0^ω`), this is the block index `i`. -/
noncomputable def firstNonzero (x : ℕ → ℕ) : ℕ :=
  if h : ∃ k, x k ≠ 0 then Nat.find h else 0

/-- The pointed gluing of a sequence of functions `(f_i : A_i → B_i)_{i ∈ ℕ}` on the
Baire space. Maps:
- `(0)^i (1) x' ↦ (0)^i (1) f_i(x')` if `x' ∈ A_i`
- `0^ω ↦ 0^ω` (and anything else to `0^ω`)
-/
noncomputable def PointedGluingFun
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) : ℕ → ℕ :=
  if hx : x.val = zeroStream then zeroStream
  else
    let i := firstNonzero x.val
    if hmem : stripZerosOne i x.val ∈ A i then
      prependZerosOne i (f i ⟨stripZerosOne i x.val, hmem⟩).val
    else zeroStream

/-!
## Regular Ordinal Sequences
-/

/-- A sequence `(α_n)_{n ∈ ℕ}` of ordinals is *regular* when for all `m ∈ ℕ` there
exists `n > m` such that `α_m ≤ α_n`. Equivalently, the sequence is cofinal
in its supremum infinitely often. -/
def IsRegularOrdSeq (α : ℕ → Ordinal.{0}) : Prop :=
  ∀ m : ℕ, ∃ n : ℕ, m < n ∧ α m ≤ α n

/-!
## Rays of Sets and Functions
-/

/-- For `B ⊆ ℕ → ℕ`, `y ∈ ℕ → ℕ`, and `n ∈ ℕ`, the *n-th ray of `B` at `y`* is:
$$\mathrm{Ray}(B, y, n) = \{x \in B \mid y|_n \sqsubseteq x \text{ and } y|_{n+1} \not\sqsubseteq x\}$$
The elements of `B` that agree with `y` on the first `n` coordinates but differ at
position `n`. This is a clopen subset of `B`. -/
def RaySet (B : Set (ℕ → ℕ)) (y : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {x ∈ B | (∀ k, k < n → x k = y k) ∧ x n ≠ y n}

/-!
## Reducibility by Pieces
-/

/-- A sequence of functions `(f_i)_{i ∈ ℕ}` is *reducible by finite pieces* to a
sequence `(g_j)_{j ∈ ℕ}` if there is a family `(I_n)_{n ∈ ℕ}` of pairwise disjoint
finite subsets of `ℕ` such that for all `n`, `f_n ≤ ⊔_{i ∈ I_n} g_i`. -/
def IsReducibleByPieces
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : ℕ → (X → Y)) (g : ℕ → (X' → Y')) : Prop :=
  ∃ (I : ℕ → Finset ℕ),
    (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
    ∀ n, ∃ (σ : X → X') (τ : Y' → Y), Continuous σ ∧ Continuous τ ∧
      ∀ x, f n x = τ (g n (σ x))

/-!
## Convergence of Sets to a Point
-/

/-- A sequence of subsets `(A_n)_{n ∈ ℕ}` of a topological space *converges* to a
point `a` if for every open neighborhood `U` of `a`, there exists `m` such that
`A_n ⊆ U` for all `n ≥ m`. -/
def SetsConvergeTo {X : Type*} [TopologicalSpace X]
    (A : ℕ → Set X) (a : X) : Prop :=
  ∀ U : Set X, IsOpen U → a ∈ U → ∃ m : ℕ, ∀ n, m ≤ n → A n ⊆ U

/-!
## CB-Rank
-/

/-- The CB-rank of a function: the supremum of ordinals `α` such that `CB_α(f)` is
nonempty. Returns `0` for functions where only `CB_0(f) = univ` is nonempty (when the
domain is empty). -/
noncomputable def CBRank {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Ordinal.{0} :=
  sSup {α : Ordinal.{0} | (CBLevel f α).Nonempty}

end
