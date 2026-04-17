import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic

open scoped Topology
open Set Function TopologicalSpace

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `2_prelim_memo.tex` — Scattered Functions and Cantor–Bendixson Analysis

This file formalizes the Cantor–Bendixson derivative for functions, the CB-rank,
and the relationship between scattered functions and the perfect kernel.

## Main definitions

* `NowhereLocllyConstant` — a function is nowhere locally constant on a set
* `CBLevel` — the Cantor–Bendixson derivative levels CB_α(f)
* `SimpleFun` — a function is simple if it has CB-degree 1

## Main results

* `scattered_iff_empty_perfectKernel_general` — f is scattered ↔ f has empty perfect kernel
* `ContinuouslyReduces.scattered` — if f ≤ g and g is scattered, then f is scattered
* `ContinuouslyReduces.cb_monotone` — if (σ,τ) reduces f to g, then σ(CB_α(f)) ⊆ CB_α(g)
-/

section NowhereLocllyConstant

/-- A function `f : X → Y` is *nowhere locally constant* if it is not constant on any
nonempty open subset of its domain. -/
def NowhereLocllyConstant {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Prop :=
  ∀ U : Set X, IsOpen U → U.Nonempty → ∃ x ∈ U, ∃ x' ∈ U, f x ≠ f x'

/-- A function is not scattered iff it admits a nonempty restriction that is nowhere
locally constant. -/
theorem not_scattered_iff_exists_nlc {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : ¬ ScatteredFun f ↔
    ∃ A : Set X, A.Nonempty ∧ NowhereLocllyConstant (f ∘ (Subtype.val : A → X)) := by
  constructor
  · intro hns
    simp only [ScatteredFun, not_forall] at hns
    push_neg at hns
    obtain ⟨S, hS, hnoU⟩ := hns
    refine ⟨S, hS, ?_⟩
    intro U hU ⟨x, hx⟩
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    have hne : (V ∩ S).Nonempty := ⟨x.val, hx, x.prop⟩
    obtain ⟨a, ⟨haV, haS⟩, b, ⟨hbV, hbS⟩, hab⟩ := hnoU V hV hne
    exact ⟨⟨a, haS⟩, haV, ⟨b, hbS⟩, hbV, hab⟩
  · rintro ⟨A, hA, hnlc⟩ hscat
    obtain ⟨U, hU, hUA, hconst⟩ := hscat A hA
    have hU' : IsOpen (Subtype.val ⁻¹' U : Set A) := hU.preimage continuous_subtype_val
    have hne : (Subtype.val ⁻¹' U : Set A).Nonempty := by
      obtain ⟨x, hxU, hxA⟩ := hUA
      exact ⟨⟨x, hxA⟩, hxU⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hnlc _ hU' hne
    exact hab (hconst a.val ⟨ha, a.prop⟩ b.val ⟨hb, b.prop⟩)

end NowhereLocllyConstant

section CBDerivative

/-!
## Cantor–Bendixson Derivative for Functions

The CB-derivative levels are defined transfinitely:
- CB₀(f) = dom f (= univ)
- CB_{α+1}(f) = CB_α(f) \ I(f, CB_α(f))
- CB_λ(f) = ⋂_{α<λ} CB_α(f) for λ limit
-/

/-- The set of `f`-isolated points in a set `A`: points where `f|_A` is locally constant. -/
def isolatedLocus {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (A : Set X) : Set X :=
  {x ∈ A | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ A, f y = f x}

/-- The isolated locus is relatively open in `A`. -/
theorem isolatedLocus_isOpen_in {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) :
    ∃ U : Set X, IsOpen U ∧ isolatedLocus f A = U ∩ A := by
  refine ⟨{x | ∃ V, IsOpen V ∧ x ∈ V ∧ ∃ c, ∀ y ∈ V ∩ A, f y = c}, ?_, ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    rintro x ⟨V, hVo, hxV, c, hc⟩
    exact ⟨V, fun y hy => ⟨V, hVo, hy, c, hc⟩, hVo, hxV⟩
  · ext x
    simp only [isolatedLocus, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨hxA, V, hV, hxV, hconst⟩
      exact ⟨⟨V, hV, hxV, f x, fun y hy => hconst y hy⟩, hxA⟩
    · rintro ⟨⟨V, hV, hxV, c, hconst⟩, hxA⟩
      refine ⟨hxA, V, hV, hxV, fun y hy => ?_⟩
      rw [hconst y hy, hconst x ⟨hxV, hxA⟩]

/-- The Cantor–Bendixson derivative levels `CB_α(f)`, defined by transfinite recursion
using `Ordinal.limitRecOn`. -/
noncomputable def CBLevel {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Ordinal.{0} → Set X :=
  fun α => Ordinal.limitRecOn α
    (univ : Set X)
    (fun β ih => ih \ isolatedLocus f ih)
    (fun β _ ih => ⋂ γ ∈ Iio β, ih γ (by exact Set.mem_Iio.mp ‹_›))

/-- CB₀(f) = univ. -/
theorem CBLevel_zero {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : CBLevel f 0 = univ := by
  simp [CBLevel, Ordinal.limitRecOn]

/-
The CB levels are decreasing: if `α ≤ β` then `CB_β(f) ⊆ CB_α(f)`.
-/
theorem CBLevel_antitone {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Antitone (CBLevel f) := by
  intro α β hαβ x hx;
  induction' β using Ordinal.limitRecOn with β ih generalizing α x;
  · aesop;
  · cases hαβ.eq_or_lt <;> simp_all +decide [ CBLevel ];
  · cases hαβ.eq_or_lt <;> simp_all +decide [ CBLevel ]

end CBDerivative

section ScatteredIffEmptyKernel

/-- The perfect kernel of `f` in terms of CB levels: the intersection of all levels. -/
noncomputable def perfectKernelCB {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) : Set X :=
  ⋂ (α : Ordinal.{0}), CBLevel f α

/-- Helper: `CBLevel f (succ α) = CBLevel f α \ isolatedLocus f (CBLevel f α)`. -/
theorem CBLevel_succ' {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (α : Ordinal.{0}) :
    CBLevel f (Order.succ α) = CBLevel f α \ isolatedLocus f (CBLevel f α) := by
  simp [CBLevel, Ordinal.limitRecOn_succ]

/-- If the perfect kernel is empty, then `f` is scattered. This is the backward direction
of Proposition 2.7. -/
theorem scattered_of_empty_perfectKernel {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (h : perfectKernelCB f = ∅) : ScatteredFun f := by
  by_contra hns
  rw [not_scattered_iff_exists_nlc] at hns
  obtain ⟨A, hA, hnlc⟩ := hns
  suffices hA_sub : ∀ α : Ordinal.{0}, A ⊆ CBLevel f α by
    exact hA.not_subset_empty (h ▸ fun x hx => mem_iInter.mpr (fun α => hA_sub α hx))
  intro α
  induction' α using Ordinal.limitRecOn with α ih _ hβ ih
  · intro x _; rw [CBLevel_zero]; exact mem_univ x
  · intro x hxA
    simp only [CBLevel, Ordinal.limitRecOn_succ]
    exact ⟨ih hxA, fun ⟨_, U, hU, hxU, hconst⟩ => by
      obtain ⟨a, ha, b, hb, hab⟩ := hnlc _ (hU.preimage continuous_subtype_val) ⟨⟨x, hxA⟩, hxU⟩
      exact hab ((hconst a.val ⟨ha, ih a.prop⟩).trans (hconst b.val ⟨hb, ih b.prop⟩).symm)⟩
  · intro x hxA
    unfold CBLevel
    rw [Ordinal.limitRecOn_limit _ _ _ _ hβ]
    exact mem_iInter₂.mpr (fun γ hγ => by exact ih γ (mem_Iio.mp hγ) hxA)

/-
If `f` is scattered and `S` is nonempty, then the isolated locus of `f` on `S`
is nonempty.
-/
lemma scattered_isolatedLocus_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) (hS : S.Nonempty) :
    (isolatedLocus f S).Nonempty := by
  rcases hf S hS with ⟨ U, hU, hU' ⟩;
  exact ⟨ hU'.1.choose, hU'.1.choose_spec.2, U, hU, hU'.1.choose_spec.1, fun x hx => hU'.2 _ ⟨ hx.1, hx.2 ⟩ _ hU'.1.choose_spec ⟩

/-
The CB levels never stabilize implies there's an injection from `Ordinal.{0}` into `X`.
Used to derive a contradiction when `X` is small enough.
-/
lemma CBLevel_strictAnti_of_ne {X Y : Type*}
    [TopologicalSpace X]
    (f : X → Y)
    (h : ∀ α : Ordinal.{0}, CBLevel f α ≠ CBLevel f (Order.succ α)) :
    ∃ g : Ordinal.{0} → X, Injective g := by
  have h_inj : ∀ α : Ordinal, ∃ x ∈ CBLevel f α, x ∉ CBLevel f (Order.succ α) := by
    intro α
    by_contra h_contra
    push_neg at h_contra
    have h_eq : CBLevel f α = CBLevel f (Order.succ α) := by
      exact Set.Subset.antisymm h_contra ( CBLevel_antitone f ( Order.le_succ α ) )
    exact h α h_eq;
  choose g hg using h_inj;
  refine' ⟨ g, fun α β hαβ => le_antisymm _ _ ⟩ <;> contrapose! hαβ;
  · have h_g_alpha_in_CBLevel_beta : g α ∈ CBLevel f (Order.succ β) := by
      exact CBLevel_antitone f ( Order.succ_le_of_lt hαβ ) ( hg α |>.1 );
    exact fun h => hg β |>.2 ( h ▸ h_g_alpha_in_CBLevel_beta );
  · intro h_eq;
    have h_subset : CBLevel f β ⊆ CBLevel f (Order.succ α) := by
      apply CBLevel_antitone;
      exact Order.succ_le_iff.mpr hαβ;
    exact hg α |>.2 ( h_eq ▸ h_subset ( hg β |>.1 ) )

/-
If `f` is scattered and `CBLevel f α` is nonempty, then `CBLevel f (succ α)` is
strictly smaller.
-/
lemma CBLevel_succ_ssubset_of_scattered {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (α : Ordinal.{0})
    (hne : (CBLevel f α).Nonempty) :
    CBLevel f (Order.succ α) ⊂ CBLevel f α := by
  have h_eq : isolatedLocus f (CBLevel f α) ≠ ∅ := by
    exact Set.Nonempty.ne_empty ( scattered_isolatedLocus_nonempty f hf _ hne );
  simp_all +decide [ Set.ssubset_def, Set.subset_def ];
  simp_all +decide [ CBLevel_succ', Set.ext_iff ];
  exact ⟨ h_eq.choose, h_eq.choose_spec.1, fun _ => h_eq.choose_spec ⟩

/-
Forward direction of Proposition 2.7 when `X` is `Small.{0}` (in particular, `Type 0`).
The CB levels are indexed by `Ordinal.{0}`, so the stabilization argument uses
`not_injective_of_ordinal` which requires `Small.{0} X`.
-/
private lemma scattered_implies_empty_perfectKernel_small {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) : perfectKernelCB f = ∅ := by
  contrapose! hf with h;
  intro h_scattered
  have h_contradiction : ∃ g : Ordinal.{0} → X, Function.Injective g := by
    apply CBLevel_strictAnti_of_ne;
    intro α h_eq;
    apply CBLevel_succ_ssubset_of_scattered f h_scattered α (by
    exact h.mono ( Set.iInter_subset _ α )) |>.ne h_eq.symm;
  exact not_injective_of_ordinal ( h_contradiction.choose ) h_contradiction.choose_spec

/-- **Proposition 2.7.** A function is scattered iff its perfect kernel is empty.

The forward direction requires showing the CB levels eventually stabilize (ordinal
arithmetic). The backward direction is fully proved above.

**Note on universes:** The proof of the forward direction uses `not_injective_of_ordinal`
which requires `Small.{0} X`. Since the CB levels are indexed by `Ordinal.{0}`, this
argument works when `X : Type 0` (or more generally when `Small.{0} X`). The theorem
is stated with `[Small.{0} X]` to reflect this constraint. -/
theorem scattered_iff_empty_perfectKernel_general {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) : ScatteredFun f ↔ perfectKernelCB f = ∅ := by
  exact ⟨scattered_implies_empty_perfectKernel_small f, scattered_of_empty_perfectKernel f⟩

end ScatteredIffEmptyKernel

section ReductionAndCB

/-!
## Proposition 2.9 (CBbasicsfromJSL)

1. If `f ≤ g` and `g` is scattered, then `f` is scattered.
2. If `(σ,τ)` continuously reduces `f` to `g`, then `σ(CB_α(f)) ⊆ CB_α(g)`.
-/

/-
If `f ≤ g` and `g` is scattered, then `f` is scattered.
-/
theorem ContinuouslyReduces.scattered {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (hred : ContinuouslyReduces f g) (hg : ScatteredFun g) :
    ScatteredFun f := by
      obtain ⟨ σ, τ, h ⟩ := hred;
      intro S hS;
      rcases hg ( σ '' S ) ( Set.Nonempty.image _ hS ) with ⟨ U, hU, hU' ⟩;
      refine' ⟨ σ ⁻¹' U, hU.preimage σ.continuous, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
      grind

/-
If `(σ,τ)` reduces `f` to `g`, then for all `α`, `σ(CB_α(f)) ⊆ CB_α(g)`.
-/
theorem ContinuouslyReduces.cb_monotone {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hσ : Continuous σ)
    (hred : ∀ x, f x = τ (g (σ x)))
    (α : Ordinal.{0}) :
    σ '' (CBLevel f α) ⊆ CBLevel g α := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx;
  induction' α using Ordinal.limitRecOn with α ih generalizing y <;> simp_all +decide [ CBLevel ];
  contrapose! hy;
  obtain ⟨ U, hUo, hyU, hU ⟩ := hy.2;
  refine' fun hy' => ⟨ _, _ ⟩;
  · exact hy';
  · refine' ⟨ σ ⁻¹' U, hUo.preimage hσ, hyU, fun z hz => _ ⟩ ; aesop;

end ReductionAndCB

section NonScatteredTheorem

/-!
## Theorem 2.5 (prop:nlc_implies_nonscattered)

If `f : X → Y` is continuous from a metrizable space to a Hausdorff space and `f` is
not scattered, then `id_ℚ` continuously reduces to `f`.

**Formalization note:** The original statement used `TopologicallyEmbedsFun (@id ℚ) f`,
which requires a *global* topological embedding `τ : Y → ℚ`. This is impossible when
`Y` is uncountable (e.g. `ℝ`), since there is no injection from an uncountable type to `ℚ`.
The corrected statement uses `ContinuouslyReduces`, which only requires continuous (not
necessarily injective) maps. Even this formulation requires `τ : Y → ℚ` to be total and
continuous, which is only possible when `Y` is zero-dimensional (since `ℚ` is totally
disconnected). A fully faithful formalization would require a notion of reduction where
`τ` is only defined on a subset of `Y`.
-/

/-
The original statement below is FALSE as formalized — `TopologicallyEmbedsFun (@id ℚ) f`
   requires an injective `τ : Y → ℚ`, which cannot exist when `Y` is uncountable.
   For example, `fun x => x^2 : ℝ → ℝ` is not scattered, but there is no injection `ℝ → ℚ`.

theorem nonscattered_embeds_idQ {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hns : ¬ ScatteredFun f) :
    TopologicallyEmbedsFun (@id ℚ) f

**Splitting Lemma.** If `g` is continuous and NLC from a pseudo-metric space to a
T₂ space, then any metric ball can be split into two smaller sub-balls with disjoint
closures whose g-images lie in disjoint open sets.
-/
lemma splitting_lemma_nlc {X Y : Type*}
    [PseudoMetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {g : X → Y} (hg : Continuous g) (hnlc : NowhereLocllyConstant g)
    (x : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ (x' : X) (ε' : ℝ),
      0 < ε' ∧ ε' < ε ∧
      Metric.closedBall x ε' ⊆ Metric.ball x ε ∧
      Metric.closedBall x' ε' ⊆ Metric.ball x ε ∧
      Disjoint (Metric.closedBall x ε') (Metric.closedBall x' ε') ∧
      ∃ (U₀ U₁ : Set Y), IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧
        g '' (Metric.ball x ε') ⊆ U₀ ∧
        g '' (Metric.ball x' ε') ⊆ U₁ := by
  -- By NLC, find x' ∈ ball(x,ε) with g(x) ≠ g(x').
  obtain ⟨x', hx'⟩ : ∃ x' ∈ Metric.ball x ε, g x ≠ g x' := by
    contrapose! hnlc;
    exact fun h => by have := h ( Metric.ball x ε ) ( Metric.isOpen_ball ) ⟨ x, Metric.mem_ball_self hε ⟩ ; obtain ⟨ x', hx', x'', hx'', hne ⟩ := this; exact hne ( hnlc x' hx' ▸ hnlc x'' hx'' ▸ rfl ) ;
  -- By T2, separate g(x) and g(x') by disjoint open U₀, U₁.
  obtain ⟨U₀, U₁, hU₀, hU₁, h_disjoint⟩ : ∃ U₀ U₁ : Set Y, IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧ g x ∈ U₀ ∧ g x' ∈ U₁ := by
    rcases t2_separation hx'.2 with ⟨ U₀, U₁, hU₀, hU₁, hU₀₁ ⟩ ; use U₀, U₁ ; aesop;
  -- By continuity, find δ₁, δ₂ > 0 with ball(x,δ₁) ⊆ g⁻¹(U₀) and ball(x',δ₂) ⊆ g⁻¹(U₁).
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, Metric.ball x δ₁ ⊆ g ⁻¹' U₀ := by
    exact Metric.mem_nhds_iff.1 ( hg.continuousAt ( hU₀.mem_nhds h_disjoint.2.1 ) )
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, Metric.ball x' δ₂ ⊆ g ⁻¹' U₁ := by
    exact Metric.mem_nhds_iff.1 ( hg.continuousAt ( hU₁.mem_nhds h_disjoint.2.2 ) );
  -- Choose ε' = min(min(min ε δ₁) δ₂)(min((ε - dist x x')/2)(dist x x' / 3)) / 2.
  obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' > 0, ε' < ε ∧ ε' < δ₁ ∧ ε' < δ₂ ∧ ε' < (ε - dist x x') / 2 ∧ ε' < dist x x' / 3 := by
    obtain ⟨ε', hε'_pos, hε'_lt⟩ : ∃ ε' > 0, ε' < min (min (min ε δ₁) δ₂) (min ((ε - dist x x') / 2) (dist x x' / 3)) := by
      refine' exists_between _;
      simp_all +decide [ Set.subset_def ];
      grind +suggestions;
    exact ⟨ ε', hε'_pos, by aesop ⟩;
  refine' ⟨ x', ε', hε'_pos, hε'_lt.1, _, _, _, _ ⟩ <;> simp_all +decide [ Set.disjoint_left ];
  · exact fun y hy => Metric.mem_ball.mpr ( lt_of_le_of_lt ( Metric.mem_closedBall.mp hy ) hε'_lt.1 );
  · intro y hy; rw [ Metric.mem_closedBall ] at hy; rw [ Metric.mem_ball ] ; linarith [ dist_triangle y x' x, dist_comm x' x ] ;
  · intro y hy; have := dist_triangle_left x x' y; have := dist_triangle_right x x' y; norm_num at *; linarith;
  · exact ⟨ U₀, hU₀, U₁, hU₁, h_disjoint.1, fun y hy => hδ₁ <| Metric.ball_subset_ball ( by linarith ) hy, fun y hy => hδ₂ <| Metric.ball_subset_ball ( by linarith ) hy ⟩

/-- **Sierpiński’s Theorem.** Every nonempty countable metrizable space without
isolated points is homeomorphic to ℚ. -/
theorem sierpinski_rat_homeomorph {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [Countable X] [Nonempty X]
    (hni : ∀ x : X, ¬ IsOpen ({x} : Set X)) :
    Nonempty (X ≃ₜ ℚ) := by
  sorry



-- 1. Define the base Cantor Space (infinite binary sequences)
abbrev CantorSpace := ℕ → Fin 2

-- 2. Define the property of being eventually zero
def IsEventuallyZero (x : CantorSpace) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, x n = 0

-- 3. Define the Subspace
def CantorEventuallyZero : Type :=
  { x : CantorSpace // IsEventuallyZero x }

instance : TopologicalSpace CantorEventuallyZero := inferInstanceAs (TopologicalSpace (Subtype _))

-- 4. Define your custom shorthand notation
-- You can use whatever symbol you prefer here.
notation "CantorRat" => CantorEventuallyZero


-- 5. Helper definitions for the tree structure (Cantor scheme)
-- A finite binary sequence can be represented as List (Fin 2).
-- You will need a function that maps a finite list to its center, radius, and open set.
structure SchemeNode (X Y : Type*) [MetricSpace X] [TopologicalSpace Y] where
  center : X
  radius : ℝ
  radius_pos : 0 < radius
  open_set : Set Y
  is_open : IsOpen open_set

-- The theorem
lemma nlc_countable_embedding_concrete {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) [Nonempty X] :
    ∃ (σ : CantorRat → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (g ∘ σ) := by

  -- We assume X has a compatible metric.
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X

  -- Step 1: Base case for the Cantor scheme.
  obtain ⟨x_empty⟩ := id ‹Nonempty X›

  -- Step 2: Define the Cantor scheme via your `splitting_lemma_nlc`.
  -- You will construct a map `scheme : List (Fin 2) → SchemeNode X Y` recursively.
  -- For brevity, we declare its existence here.
  have construct_scheme : ∃ (scheme : List (Fin 2) → SchemeNode X Y),
      ∀ s : List (Fin 2),
        (scheme (s ++ [0])).center = (scheme s).center ∧
        (scheme (s ++ [0])).radius = (scheme (s ++ [1])).radius ∧
        (scheme (s ++ [0])).radius ≤ (scheme s).radius / 2 ∧
        Disjoint (scheme (s ++ [0])).open_set (scheme (s ++ [1])).open_set := by
    -- Here you apply `splitting_lemma_nlc` recursively.
    sorry

  obtain ⟨scheme, h_scheme⟩ := construct_scheme

  -- Step 3: Define σ : CantorRat → X
  -- Since every x ∈ CantorRat is eventually zero, it has a "last" index where it might be 1.
  -- We can truncate `x.val` to a `List (Fin 2)` up to that index, say `s`.
  -- Then σ(x) is simply defined as `(scheme s).center`.

  have extract_prefix : CantorRat → List (Fin 2) := by
    intro x
    -- Extract the finite prefix before the infinite tail of zeros.
    -- (Implementation requires `Nat.find` on the `IsEventuallyZero` property).
    sorry

  let σ : CantorRat → X := fun x => (scheme (extract_prefix x)).center

  -- Step 4: Prove σ is an embedding.
  have hσ_embed : Topology.IsEmbedding σ := by
    -- Proof strategy:
    -- 1. σ is injective because diverging finite prefixes map to disjoint closed balls.
    -- 2. σ is continuous because the radii ρ_s ≤ 2^{-|s|} shrink to 0.
    -- 3. σ is open onto its image because cylinder sets in CantorRat map to
    --    intersections of open balls with the image σ(CantorRat).
    sorry

  -- Step 5: Prove g ∘ σ is an embedding.
  have hgσ_embed : Topology.IsEmbedding (g ∘ σ) := by
    -- Proof strategy mirroring Kechris:
    -- Show that for any cylinder set N_s in CantorSpace,
    -- (g ∘ σ)(CantorRat ∩ N_s) = (g ∘ σ)(CantorRat) ∩ U_s
    -- The disjointness of U_{s ⌢ 0} and U_{s ⌢ 1} separates the branches,
    -- making the restricted map an open bijection onto its image.
    sorry

  -- Conclusion
  exact ⟨σ, hσ_embed, hgσ_embed⟩

/-- **Cantor scheme construction.** If `g : X → Y` is continuous and NLC from a
nonempty metrizable space to a T₂ space, then there exists a countable nonempty
subset `S ⊆ X` such that:
- `S` has no isolated points (in the subspace topology)
- The restriction of `g` to `S` is a topological embedding into `Y` -/
lemma nlc_countable_embedding {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) [Nonempty X] :
    ∃ (S : Set X), S.Countable ∧ S.Nonempty ∧
      (∀ x : S, ¬ IsOpen ({x} : Set S)) ∧
      Topology.IsEmbedding (fun (x : S) => g x.val) := by
  sorry

/-- **Key helper for Theorem 2.5.** If `g : X → Y` is continuous from a nonempty
metrizable space to a T₂ space, and `g` is nowhere locally constant, then there exists
a topological embedding `σ : ℚ → X` such that `g ∘ σ` is also a topological embedding. -/
lemma nlc_to_rat_embedding {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) [Nonempty X] :
    ∃ (σ : ℚ → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (g ∘ σ) := by
  obtain ⟨S, hcount, hne, hni, hemb_g⟩ := nlc_countable_embedding g hg hnlc
  haveI : Countable S := hcount.to_subtype
  haveI : Nonempty S := hne.to_subtype
  obtain ⟨h⟩ := sierpinski_rat_homeomorph hni
  exact ⟨Subtype.val ∘ h.symm,
    Topology.IsEmbedding.subtypeVal.comp h.symm.isEmbedding,
    hemb_g.comp h.symm.isEmbedding⟩

/-- **Theorem 2.5 (weakened formulation).** If `f` is continuous from a metrizable to a
Hausdorff space and not scattered, then there exists a topological embedding `σ : ℚ → X`
such that `f ∘ σ` is also a topological embedding (into `Y`). -/
theorem nonscattered_embeds_idQ {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) (hns : ¬ ScatteredFun f) :
    ∃ (σ : ℚ → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (f ∘ σ) := by
  rw [not_scattered_iff_exists_nlc] at hns
  obtain ⟨A, hA, hnlc⟩ := hns
  haveI : Nonempty A := hA.to_subtype
  have hcont : Continuous (f ∘ Subtype.val : A → Y) := hf.comp continuous_subtype_val
  obtain ⟨σ, hσ, hgσ⟩ := nlc_to_rat_embedding (f ∘ Subtype.val) hcont hnlc
  exact ⟨Subtype.val ∘ σ,
    Topology.IsEmbedding.subtypeVal.comp hσ,
    hgσ⟩

end NonScatteredTheorem

section SimpleFunctions

/-- A function is simple if it is scattered and has CB-degree 1: the last CB-level
maps to a single point. -/
def SimpleFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ScatteredFun f ∧
  ∃ α : Ordinal.{0},
    (CBLevel f α).Nonempty ∧
    CBLevel f (Order.succ α) = ∅ ∧
    ∃ y, ∀ x ∈ CBLevel f α, f x = y

end SimpleFunctions

section FirstReductionTheorem

/-!
## Theorem 2.12 (FirststepforBQOthm)

Every continuous function from a zero-dimensional separable metrizable space to a
metrizable space is either scattered, equivalent to `id_ℚ`, or equivalent to `id_{ℕ→ℕ}`.
-/

/-- **First Reduction Theorem.** Every continuous function from a zero-dimensional
separable metrizable space to a metrizable space is either scattered, or continuously
equivalent to `id_ℚ`, or continuously equivalent to `id_{ℕ → ℕ}`.

This theorem combines deep results: the Cantor scheme construction (Theorem 2.5),
universality results for `ℚ` and the Baire space `ℕ → ℕ`, and the Perfect Function
Property. -/
theorem first_reduction_theorem
    {X Y : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : X → Y} (hf : Continuous f) :
    ScatteredFun f ∨
    ContinuouslyEquiv f (@id ℚ) ∨
    ContinuouslyEquiv f (@id (ℕ → ℕ)) := by
  sorry

end FirstReductionTheorem

section DecompositionLemma

/-!
## Lemma 2.15 (DecompositionLemma)

Any scattered function from a zero-dimensional separable metrizable space is locally
simple.

The proof requires several ingredients:
1. **Clopen basis**: In a metrizable totally disconnected space, every open set
   containing a point has a clopen subset containing that point. This is de Groot's
   theorem: metrizable + totally disconnected → ultra-metrizable, and in an
   ultrametric space, all balls are clopen.
2. **CB analysis of restrictions**: The CB levels of a restriction relate to the
   CB levels of the original function.
3. **Local simplicity**: Using the CB rank of each point and the clopen basis,
   we find a clopen neighborhood on which the function is simple.
-/

/-- **Helper (clopen basis).** In a metrizable, separable, totally disconnected space,
every open set containing a point has a clopen subset containing that point.
This is a consequence of de Groot's theorem (metrizable + TD → ultra-metrizable)
and the fact that balls in an ultrametric space are clopen. -/
lemma exists_clopen_subset_of_open {X : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  sorry

/-- **Helper.** A constant function on a nonempty subtype is simple. -/
lemma simpleFun_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} (hU : U.Nonempty) (y : Y) :
    SimpleFun (fun (_ : U) => y) := by
  refine ⟨fun S hS => ⟨univ, isOpen_univ, ⟨hS.some, trivial, hS.some_mem⟩,
    fun _ _ _ _ => rfl⟩, 0, ⟨⟨hU.some, hU.some_mem⟩, by simp [CBLevel_zero]⟩, ?_, y, fun x _ => rfl⟩
  rw [CBLevel_succ', CBLevel_zero]
  ext ⟨z, hz⟩
  simp only [mem_diff, mem_univ, true_and, mem_empty_iff_false, iff_false, not_not]
  exact ⟨trivial, univ, isOpen_univ, trivial, fun _ _ => rfl⟩

/-- **Decomposition Lemma.** Any scattered function from a zero-dimensional separable
metrizable space is locally simple: around each point there is a clopen neighborhood
on which `f` is simple.

The proof uses `exists_clopen_subset_of_open` (clopen basis) and the CB analysis.
Given `x`, the scatteredness of `f` provides an open `U` and a value `y` such that
`f` is constantly `y` on `U ∩ {x}`. Using the CB rank of `x`, we find an open set
where `f` is constant on the relevant CB level, then refine to a clopen subset. -/
theorem decomposition_lemma {X Y : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    [TopologicalSpace Y]
    {f : X → Y} (hf : ScatteredFun f) :
    ∀ x : X, ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
      SimpleFun (f ∘ (Subtype.val : U → X)) := by
  sorry

end DecompositionLemma