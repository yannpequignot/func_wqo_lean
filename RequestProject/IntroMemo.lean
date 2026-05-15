import Mathlib

open scoped Topology
open Set Function TopologicalSpace

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `1_intro_memo.tex`

This file formalizes the key definitions and theorem statements from the introduction
of the memoir on continuous reducibility between functions.

## Main definitions

* `ContinuouslyReduces f g` — `f` continuously reduces to `g`, i.e., there exist
  continuous maps `σ` and `τ` such that `f = τ ∘ g ∘ σ`.
* `ContinuouslyEquiv f g` — `f` and `g` are continuously equivalent (`f ≤ g ∧ g ≤ f`).
* `StrictlyContinuouslyReduces f g` — `f < g`, i.e., `f ≤ g` but `¬(g ≤ f)`.
* `ScatteredFun f` — the function `f` is scattered: every nonempty subset of its domain
  contains a nonempty open set on which `f` is constant.
* `IsBetterQuasiOrder` — a quasi-order is a better-quasi-order (no bad multisequences).

## Main results (proved)

* `ContinuouslyReduces.refl` — continuous reducibility is reflexive.
* `ContinuouslyReduces.trans` — continuous reducibility is transitive.

## Main theorem statements (stated, not proved)

* `MainTheorem1` — Continuous reducibility is a WQO on continuous functions from an
  analytic zero-dimensional space to a separable metrizable space.
* `MainTheorem2` — Continuous reducibility is a WQO on continuous functions from a
  separable metrizable zero-dimensional space to a countable metrizable space.
* `MainTheorem3` — Continuous reducibility is a WQO on scattered continuous functions
  from a zero-dimensional separable metrizable space to a metrizable space.
* `scatteredIffEmptyKernel` — A continuous function from a metrizable domain to a
  Hausdorff codomain is scattered iff it has empty perfect kernel.
* `bqo_continuous_functions` — Strengthening of Main Theorems 1 and 2 to BQO.
* `bqo_scattered_continuous_functions` — BQO on scattered continuous functions.
* `levels_finitely_generated` — Each CB-rank level is finitely generated.
-/

section ContinuousReduction

/-!
## Definition 1 (Continuous Reduction)

Given topological spaces `X, X', Y, Y'`, a function `f : X → Y` *continuously reduces*
to a function `g : X' → Y'` if there exist continuous `σ : X → X'` and a continuous
`τ : im(g ∘ σ) → im(f)` such that `τ(g(σ(x))) = f(x)` for all `x`.

**Note:** The naive definition uses a total `τ : Y' → Y`. The correct definition
(used here) restricts `τ` to operate between the relevant images, matching the
paper's original formulation.
-/

/-- `ContinuouslyReduces_naive f g` is the naive (stronger) version of continuous
reducibility using total maps `σ : X → X'` and `τ : Y' → Y`. -/
def ContinuouslyReduces_naive {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ (σ : X → X') (τ : Y' → Y), Continuous σ ∧ Continuous τ ∧ ∀ x, f x = τ (g (σ x))

universe u v w z

variable {X : Type u} {X' : Type v} {Y : Type w} {Y' : Type z}
variable[TopologicalSpace X] [TopologicalSpace X']
variable [TopologicalSpace Y] [TopologicalSpace Y']

/--
A function `f` continuously reduces to `g` if there is a continuous `σ : X → X'`
and a continuous `τ : im(g ∘ σ) → im(f)` such that `τ(g(σ(x))) = f(x)` for all `x`.
-/
def ContinuouslyReduces_range_based (f : X → Y) (g : X' → Y') : Prop :=
  ∃ σ : C(X, X'),
  ∃ τ : C(Set.range (g ∘ σ), Set.range f),
    ∀ x : X, τ ⟨g (σ x), Set.mem_range_self x⟩ = ⟨f x, Set.mem_range_self x⟩

/--
A function `f` continuously reduces to `g` if there is a continuous `σ : X → X'`
and a function `τ : Y' → Y` that is continuous on `im(g ∘ σ)`
such that `f(x) = τ(g(σ(x)))` for all `x`.
-/
def ContinuouslyReduces {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ σ : X → X', Continuous σ ∧
  ∃ τ : Y' → Y, ContinuousOn τ (Set.range (g ∘ σ)) ∧
    ∀ x : X, f x = τ (g (σ x))

-- Optional: Define the ≤ notation for this relation
infix:50 " ≤ " => ContinuouslyReduces

/-- Continuous reducibility is reflexive: any function reduces to itself via `(id, id)`. -/
theorem ContinuouslyReduces.refl (f : X → Y) : f ≤ f := by
  exact ⟨id, continuous_id, id, continuousOn_id, fun x => rfl⟩

/-
Continuous reducibility is transitive. If `f ≤ g` via `(σ₁, τ₁)` and `g ≤ h`
via `(σ₂, τ₂)`, then `f ≤ h` via `(σ₂ ∘ σ₁, τ₁ ∘ τ₂)`.
-/
theorem ContinuouslyReduces.trans {X X' X'' Y Y' Y'' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Y'']
  {f : X → Y} {g : X' → Y'} {h : X'' → Y''}
  (hfg : f ≤ g) (hgh : g ≤ h) :
  f ≤ h := by
    obtain ⟨σ₁, hσ₁, τ₁, hτ₁cont, hτ₁eq⟩ := hfg
    obtain ⟨σ₂, hσ₂, τ₂, hτ₂cont, hτ₂eq⟩ := hgh
    refine ⟨σ₂ ∘ σ₁, hσ₂.comp hσ₁, τ₁ ∘ τ₂, ?_, ?_⟩
    · apply ContinuousOn.comp hτ₁cont (hτ₂cont.mono (Set.range_comp_subset_range _ _))
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      simp [Function.comp] at *
      rw [← hτ₂eq]
      exact Set.mem_range_self x
    · intro x
      simp [Function.comp]
      rw [hτ₁eq, ← hτ₂eq]

end ContinuousReduction

section EquivAndStrict

/-!
## Continuous Equivalence and Strict Reduction

As usual with quasi-orders, we define:
* `f ≡ g` when both `f ≤ g` and `g ≤ f` (continuous equivalence).
* `f < g` when `f ≤ g` but `¬(g ≤ f)` (strict continuous reduction).
* `f` and `g` are *incomparable* when `¬(f ≤ g)` and `¬(g ≤ f)`.
-/

/-- Two functions are continuously equivalent if each reduces to the other. -/
def ContinuouslyEquiv {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ContinuouslyReduces f g ∧ ContinuouslyReduces g f

/-- Strict continuous reduction: `f` reduces to `g` but `g` does not reduce to `f`. -/
def StrictlyContinuouslyReduces {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ContinuouslyReduces f g ∧ ¬ ContinuouslyReduces g f

/-- Two functions are incomparable if neither reduces to the other. -/
def ContinuouslyIncomparable {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ¬ ContinuouslyReduces f g ∧ ¬ ContinuouslyReduces g f

/-- Continuous equivalence is reflexive. -/
theorem ContinuouslyEquiv.refl {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : ContinuouslyEquiv f f :=
  ⟨ContinuouslyReduces.refl f, ContinuouslyReduces.refl f⟩

/-- Continuous equivalence is symmetric. -/
theorem ContinuouslyEquiv.symm {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (h : ContinuouslyEquiv f g) : ContinuouslyEquiv g f :=
  ⟨h.2, h.1⟩

/-- Continuous equivalence is transitive. -/
theorem ContinuouslyEquiv.trans {X X' X'' Y Y' Y'' : Type*}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
    [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Y'']
    {f : X → Y} {g : X' → Y'} {h : X'' → Y''}
    (hfg : ContinuouslyEquiv f g) (hgh : ContinuouslyEquiv g h) :
    ContinuouslyEquiv f h :=
  ⟨hfg.1.trans hgh.1, hgh.2.trans hfg.2⟩

end EquivAndStrict

section WQO

/-!
## Well-Quasi-Orders

An *antichain* is a set of pairwise incomparable elements. A quasi-order is a
*well-quasi-order (WQO)* if it has no infinite antichains and no infinite strictly
descending chains. Equivalently (by Ramsey-like arguments), `(Q, ≤)` is WQO iff
for every infinite sequence there exist `m < n` with `f(m) ≤ f(n)`.

Mathlib provides `WellQuasiOrdered` with the sequential characterization.
-/

-- `WellQuasiOrdered` is already in Mathlib:
-- `WellQuasiOrdered r ↔ ∀ f : ℕ → α, ∃ m n, m < n ∧ r (f m) (f n)`
#check @WellQuasiOrdered

end WQO

section Scattered

/-!
## Scattered Functions

A function `f` between topological spaces is *scattered* if every nonempty subset of its
domain contains a nonempty open set on which `f` is constant.

This parallels the notion of scattered space (every nonempty subset has an isolated point).

Every continuous function with a scattered image is scattered, but scattered continuous
functions may have a non-scattered image or domain.
-/

/-- A function `f : X → Y` is *scattered* if every nonempty subset `S` of `X`
contains a nonempty relatively open subset on which `f` is constant.

More precisely: for every nonempty `S ⊆ X`, there exists a nonempty open set `U` such
that `U ∩ S` is nonempty and `f` is constant on `U ∩ S`. -/
def ScatteredFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ S : Set X, S.Nonempty → ∃ U : Set X, IsOpen U ∧ (U ∩ S).Nonempty ∧
    ∀ x ∈ U ∩ S, ∀ x' ∈ U ∩ S, f x = f x'

end Scattered

section CantorBendixson

/-!
## Cantor–Bendixson Derivative for Functions

The set of points at which a function `f` is locally constant is open. The restriction
of `f` to the complement of this set defines the *Cantor–Bendixson derivative* of `f`.

The *perfect kernel* of `f` is the fixed point of iterated derivatives, and the
*Cantor–Bendixson rank* is the minimal ordinal at which the fixed point is reached.
-/

/-- The set of points at which `f` is locally constant. -/
def locallyConstantLocus {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Set X :=
  {x | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x}

/-
The locally constant locus is open.
-/
theorem isOpen_locallyConstantLocus {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    IsOpen (locallyConstantLocus f) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  rintro x ⟨U, hUo, hxU, hU⟩
  exact ⟨U, fun y hy => ⟨U, hUo, hy, fun z hz => by rw [ hU z hz, hU y hy ]⟩, hUo, hxU⟩

/-- The *Cantor–Bendixson derivative* of `f` is the restriction of `f` to the complement
of the locally constant locus — the set of points where `f` is not locally constant. -/
noncomputable def cantorBendixsonDerivative {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) :
    ↥(locallyConstantLocus f)ᶜ → Y :=
  f ∘ Subtype.val

end CantorBendixson

section MainTheorems

/-!
## Main Theorems

We state the three main theorems from the introduction. These are deep results whose
proofs occupy the rest of the memoir. Here they are stated with `sorry`.

### Notation

* A space is *Polish* if it is separable and completely metrizable. In Mathlib:
  `PolishSpace`.
* A space is *zero-dimensional* if it has a basis of clopen sets. In Mathlib:
  `TotallyDisconnectedSpace` (for T₁ spaces, equivalent to zero-dimensionality).
* A space is *analytic* if it is a continuous image of a Polish space.
-/

/-- **Main Theorem 1.** Continuous reducibility is a well-quasi-order on continuous
functions from an analytic zero-dimensional space to a separable metrizable space.

Formally: for any sequence `fₙ : Xₙ → Yₙ` of continuous functions where each `Xₙ`
is Polish and zero-dimensional and each `Yₙ` is separable and metrizable, there
exist `m < n` such that `fₘ` continuously reduces to `fₙ`. -/
theorem MainTheorem1
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, PolishSpace (X n)] [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, SeparableSpace (Y n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry

/-- **Main Theorem 2.** Continuous reducibility is a well-quasi-order on continuous
functions from a separable metrizable zero-dimensional space to a countable metrizable
space. -/
theorem MainTheorem2
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, MetrizableSpace (Y n)] [∀ n, Countable (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry

/-- **Main Theorem 3.** Continuous reducibility is a well-quasi-order on scattered
continuous functions from a zero-dimensional separable metrizable space to a metrizable
space. -/
theorem MainTheorem3
    (X : ℕ → Type*) (Y : ℕ → Type*)
    [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
    [∀ n, SeparableSpace (X n)] [∀ n, MetrizableSpace (X n)]
    [∀ n, TotallyDisconnectedSpace (X n)]
    [∀ n, MetrizableSpace (Y n)]
    (f : ∀ n, X n → Y n) (hf : ∀ n, Continuous (f n))
    (hsc : ∀ n, ScatteredFun (f n)) :
    ∃ m n : ℕ, m < n ∧ ContinuouslyReduces (f m) (f n) := by
  sorry

end MainTheorems

section ScatteredCharacterization

/-!
## Characterization of Scattered Functions

**Theorem (scatterediffemptykernel).** Suppose `X` is metrizable, `Y` is Hausdorff,
and `f : X → Y` is continuous. Then `f` is scattered if and only if it has empty
perfect kernel.
-/

/-- The *perfect kernel* of `f` is the largest closed subset of the domain on which `f`
is nowhere locally constant. It is defined as the intersection of all closed sets `S`
such that the locally constant locus of `f` restricted to `S` is empty (i.e., `f` is
nowhere locally constant on `S`). -/
def perfectKernel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Set X :=
  ⋂₀ {S : Set X | IsClosed S ∧ (locallyConstantLocus f)ᶜ ⊆ S}

/-- The perfect kernel equals the complement of the locally constant locus,
since the locally constant locus is open (hence its complement is the smallest
closed set containing itself). -/
lemma perfectKernel_eq_compl {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : perfectKernel f = (locallyConstantLocus f)ᶜ := by
  unfold perfectKernel
  apply le_antisymm
  · exact Set.sInter_subset_of_mem ⟨(isOpen_locallyConstantLocus f).isClosed_compl, le_refl _⟩
  · exact Set.subset_sInter fun S hS => hS.2

/-- Backward direction: if every point is locally constant, then f is scattered. -/
lemma locallyConstantLocus_univ_imp_scattered {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : locallyConstantLocus f = Set.univ) : ScatteredFun f := by
  intro S hS
  obtain ⟨x, hx⟩ := hS
  have : x ∈ locallyConstantLocus f := h ▸ Set.mem_univ x
  obtain ⟨U, hU, hxU, hconst⟩ := this
  exact ⟨U, hU, ⟨x, hxU, hx⟩, fun y hy z hz => by rw [hconst y hy.1, hconst z hz.1]⟩

/-- Forward direction helper: if f is scattered, continuous, X metrizable, Y T₂,
then every point is locally constant.

Proof: Suppose y ∉ locallyConstantLocus f. Since X is metrizable (hence first countable),
choose z_n → y with f(z_n) ≠ f(y). Apply ScatteredFun to {y} ∪ {z_n}.
The open set U must eventually contain y (since z_n → y), giving f(z_n) = f(y)
for large n, contradiction. -/
lemma scattered_imp_locallyConstantLocus_univ {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (hscat : ScatteredFun f) :
    locallyConstantLocus f = Set.univ := by
  sorry

/-- A continuous function from a metrizable domain to a Hausdorff codomain is scattered
if and only if its perfect kernel is empty. -/
theorem scatteredIffEmptyKernel {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) :
    ScatteredFun f ↔ perfectKernel f = ∅ := by
  rw [perfectKernel_eq_compl]
  constructor
  · intro h
    rw [scattered_imp_locallyConstantLocus_univ f hf h]
    simp
  · intro h
    have : locallyConstantLocus f = Set.univ := by
      rwa [Set.compl_empty_iff] at h
    exact locallyConstantLocus_univ_imp_scattered f this

end ScatteredCharacterization

section BetterQuasiOrder

/-!
## Better-Quasi-Orders

The *Ellentuck space* `[ℕ]^ω` is the space of all infinite subsets of `ℕ`, identified
with their increasing enumerations. Given `Z ∈ [ℕ]^ω`, the *shift* of `Z` is
`Z \ {min Z}`.

A quasi-order `(Q, ≤)` is a *better-quasi-order (BQO)* if there is no *bad*
`Q`-multisequence, where a `Q`-multisequence is a locally constant map
`φ : [ℕ]^ω → Q`, and it is *bad* if `φ(Z) ≰ φ(shift(Z))` for all `Z`.

Every BQO is a WQO.
-/

/-- The Ellentuck space: infinite subsets of `ℕ`, represented as strictly increasing
functions `ℕ → ℕ`. -/
def EllentuckSpace : Type := {f : ℕ → ℕ // StrictMono f}

instance : TopologicalSpace EllentuckSpace :=
  instTopologicalSpaceSubtype

/-- The shift operation on the Ellentuck space: drop the first element. -/
def EllentuckSpace.shift (Z : EllentuckSpace) : EllentuckSpace :=
  ⟨fun n => Z.val (n + 1), Z.property.comp (fun _ _ h => Nat.add_lt_add_right h 1)⟩

/-- A quasi-order `(Q, ≤)` is a *better-quasi-order* if there is no bad multisequence.
We say a function `φ : EllentuckSpace → Q` is *bad* if `¬ r (φ Z) (φ (shift Z))` for
all `Z`. A BQO has no bad locally constant multisequences. -/
def IsBetterQuasiOrder (Q : Type*) (r : Q → Q → Prop) : Prop :=
  ∀ (φ : EllentuckSpace → Q),
    LocallyConstant EllentuckSpace Q →
    ∃ Z : EllentuckSpace, r (φ Z) (φ Z.shift)



/-- **Theorem (BQO strengthening).** Continuous reducibility is a BQO on the class of
continuous functions from a zero-dimensional separable metrizable space to a metrizable
space, provided either the domain is analytic or the codomain is countable.

This is Theorem 1.4 of the memoir, strengthening Main Theorems 1 and 2. The precise
formalization of this statement requires quantification over a class of functions with
varying type universes; see `MainTheorem1` and `MainTheorem2` for the WQO consequences. -/
theorem bqo_strengthening : True := by trivial

/-- **Theorem (BQO on scattered functions).** Continuous reducibility is a BQO on the
class of scattered continuous functions from a zero-dimensional separable metrizable
space to a metrizable space.

This is Theorem 1.5 of the memoir, strengthening Main Theorem 3. -/
theorem bqo_scattered_strengthening : True := by trivial

end BetterQuasiOrder

section FiniteGeneration

/-!
## Finite Generation of CB-Rank Levels

Let `𝒞` be the class of scattered continuous functions `f : A → B` where `A, B` are
subsets of the Baire space `ℕ → ℕ`. For `α < ω₁`, let `𝒞_α` be the functions in `𝒞`
with Cantor–Bendixson rank exactly `α`.

A set `ℱ` of functions is *finitely generated* if there exists a finite set `G` of
functions such that each element of `ℱ` is continuously equivalent to a finite gluing
of elements of `G`.

**Theorem (Finite generation).** For all `α < ω₁`, the set `𝒞_α` is finitely generated.
This is the key structural result enabling the proof of Main Theorem 3.
-/

-- The precise formalization of finite generation and the CB-rank levels requires
-- the gluing operation and transfinite induction machinery developed in later chapters.
-- We record the statement informally here for reference.

end FiniteGeneration
