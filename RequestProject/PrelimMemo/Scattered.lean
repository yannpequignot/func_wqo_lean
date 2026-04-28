import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.GenRedProp

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

/-!
## CB-Rank
-/

/-- The CB-rank of a  SCATTERED function can be defined by the supremum of ordinals `α` such that `CB_α(f)` is
nonempty. Returns `0` for functions where only `CB_0(f) = univ` is nonempty (when the
domain is empty). -/


noncomputable def CBRank_scat {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (fs: ScatteredFun f) : Ordinal.{0} :=
  sSup {α : Ordinal.{0} | (CBLevel f α).Nonempty}

/- In general we define the CB rank as the least ordinal such that the CB derivative stabilizes-/
noncomputable def CBRank {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | (CBLevel f α) = (CBLevel f (Order.succ α))}



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

lemma local_cb_derivative {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y}
    (U: Set X) (hU: IsOpen U)
    (α : Ordinal.{0}):
    CBLevel (f ∘ (Subtype.val: U -> X)) α= (CBLevel f α) ∩ U := by
  induction' α using Ordinal.limitRecOn with α ih;
  · simp +decide [ CBLevel ];
  · rw [ CBLevel_succ', CBLevel_succ' ];
    simp +decide [ Set.ext_iff, isolatedLocus ] at ih ⊢;
    intro x;
    constructor;
    · rintro ⟨ hx, hx', hx'' ⟩;
      refine' ⟨ ⟨ ih x |>.1 ⟨ hx, hx' ⟩ |>.1, _ ⟩, hx ⟩;
      intro V hV hxV;
      specialize hx'' ( Subtype.val ⁻¹' V ) ( hV.preimage continuous_subtype_val ) ( by simpa );
      grind;
    · intro hx;
      refine' ⟨ hx.2, ih x |>.2 ⟨ hx.1.1, hx.2 ⟩ |>.2, _ ⟩;
      intro V hV hxV;
      rcases hV with ⟨ W, hW, rfl ⟩;
      rcases hx.1.2 ( W ∩ U ) ( hW.inter hU ) ⟨ hxV, hx.2 ⟩ with ⟨ y, hyW, hyU, hy ⟩;
      exact ⟨ y, hyW.2, hyW.1, ih y |>.2 ⟨ hyU, hyW.2 ⟩ |>.2, hy ⟩;
  · rename_i o ho ih;
    refine' Set.Subset.antisymm _ _;
    · intro x hx;
      simp_all +decide [ CBLevel, Set.ext_iff ];
      exact ⟨ fun i hi => ( ih i hi x |> Iff.mp ) ( hx i |> fun ⟨ hx₁, hx₂ ⟩ => ⟨ hx₁, hx₂ hi ⟩ ) |>.1, hx o |> fun ⟨ hx₁, hx₂ ⟩ => hx₁ ⟩;
    · intro x hx;
      simp_all +decide [ CBLevel, Set.ext_iff ];
      exact fun i hi => ih i hi x |>.2 ⟨ hx.1 i hi, hx.2 ⟩ |>.2

/-- The exit ordinal of x (min α s.t. x ∉ CBLevel f α) cannot be a limit ordinal. -/
lemma exit_ordinal_not_limit {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (x : X) (γ : Ordinal.{0})
    (hx_out : x ∉ CBLevel f γ)
    (hγ_limit : Order.IsSuccLimit γ) :
    ∃ δ : Ordinal.{0}, δ < γ ∧ x ∉ CBLevel f δ := by
  by_contra h
  push_neg at h
  apply hx_out
  simp [CBLevel, Ordinal.limitRecOn_limit _ _ _ _ hγ_limit]
  intro δ hδ
  exact h δ hδ

/-
The minimal exit ordinal of any point from the CB hierarchy is a successor.
-/
lemma exit_ordinal_is_successor {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (x : X) (γ : Ordinal.{0})
    (hx_out : x ∉ CBLevel f γ) :
    ∃ β : Ordinal.{0}, β < γ ∧ x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
  contrapose! hx_out;
  induction' γ using Ordinal.limitRecOn with γ ih;
  · exact CBLevel_zero f ▸ Set.mem_univ x;
  · exact hx_out γ ( Order.lt_succ γ ) ( ih fun β hβ => hx_out β ( lt_trans hβ ( Order.lt_succ γ ) ) );
  · simp_all +decide [ CBLevel ];
    grind

/-
If x ∈ isolatedLocus f (CBLevel f β), then there exists open U with x ∈ U
    such that CBLevel f (succ β) ∩ U = ∅.
-/
lemma isolatedLocus_clears_succ_level {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (β : Ordinal.{0})
    (x : X)
    (hx : x ∈ isolatedLocus f (CBLevel f β)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ := by
  rcases hx with ⟨ hx₁, ⟨ U, hU₁, hx₂, hx₃ ⟩ ⟩;
  refine' ⟨ U, hU₁, hx₂, Set.eq_empty_iff_forall_notMem.2 fun y hy => _ ⟩;
  simp_all +decide [ CBLevel_succ' ];
  exact hy.1.2 ⟨ hy.1.1, U, hU₁, hy.2, fun z hz => by aesop ⟩

/-
If CBLevel f (succ β) ∩ U = ∅ for open U, then CBRank(f|_U) ≤ succ β,
    provided succ β < omega1.
-/
lemma cbrank_restriction_le_of_empty_level {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    (U : Set X) (hU : IsOpen U)
    (β : Ordinal.{0})
    (hempty : CBLevel f (Order.succ β) ∩ U = ∅) :
    CBRank (f ∘ (Subtype.val : U → X)) ≤ Order.succ β := by
  apply csInf_le';
  ext x;
  constructor <;> intro hx <;> contrapose! hempty;
  · exact ⟨ x, by simpa using local_cb_derivative U hU ( Order.succ β ) |>.subset ⟨ x, hx, rfl ⟩ ⟩;
  · contrapose! hempty; simp_all +decide [ CBLevel_succ' ] ;

lemma limit_locally_lower {X Y : Type*}
    [TopologicalSpace X]
    [TopologicalSpace Y]
    {f : X → Y}
    (hf : ScatteredFun f)
    (lam : Ordinal)
    (hlam : lam = CBRank f)
    (hlim : Order.IsSuccLimit lam) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ CBRank (f ∘ (Subtype.val : U → X)) < lam := by
  intro x
  by_cases h_empty_level : (CBLevel f lam).Nonempty;
  · have h_contradiction : ∀ α, CBLevel f α = CBLevel f (Order.succ α) → CBLevel f α = ∅ := by
      intro α hα
      by_contra h_nonempty
      have h_contradiction : CBLevel f (Order.succ α) ⊂ CBLevel f α := by
        apply CBLevel_succ_ssubset_of_scattered f hf α (Set.nonempty_iff_ne_empty.mpr h_nonempty)
      simp_all +decide [ Set.ssubset_def ];
    contrapose! h_contradiction;
    exact ⟨ lam, hlam ▸ csInf_mem ( show { α : Ordinal.{0} | CBLevel f α = CBLevel f ( Order.succ α ) }.Nonempty from by exact Set.nonempty_iff_ne_empty.2 fun h => by simp_all +decide [ CBRank ] ), h_empty_level ⟩;
  · simp_all +decide [ Set.not_nonempty_iff_eq_empty ];
    have h_contradiction : ∃ β, β < CBRank f ∧ x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
      apply exit_ordinal_is_successor;
      aesop;
    obtain ⟨β, hβ_lt, hβ_mem, hβ_not_mem⟩ := h_contradiction
    have h_iso_loc : x ∈ isolatedLocus f (CBLevel f β) := by
      simp_all +decide [ CBLevel_succ' ]
    have h_neighborhood : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ := by
      obtain ⟨U, hU_open, hxU, hU_const⟩ := h_iso_loc.2
      refine ⟨U, hU_open, hxU, ?_⟩
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy_succ hyU
      rw [CBLevel_succ'] at hy_succ
      exact hy_succ.2 ⟨hy_succ.1, U, hU_open, hyU,
        fun z hz => (hU_const z hz).trans (hU_const y ⟨hyU, hy_succ.1⟩).symm⟩
    obtain ⟨U, hU_open, hxU, hU_empty⟩ := h_neighborhood
    have h_cbrank_le : CBRank (f ∘ (Subtype.val : U → X)) ≤ Order.succ β := by
      apply cbrank_restriction_le_of_empty_level U hU_open β hU_empty
    exact ⟨U, hU_open, hxU, lt_of_le_of_lt h_cbrank_le (hlim.succ_lt hβ_lt)⟩

/-!
## Proposition 2.9 (CBbasicsfromJSL)

1. If `f ≤ g` and `g` is scattered, then `f` is scattered.
2. If `(σ,τ)` continuously reduces `f` to `g`, then `σ(CB_α(f)) ⊆ CB_α(g)`.
-/

lemma ContinuouslyReduces.scattered_local {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (σ : X → X') (τ : Y' → Y) -- express continuously reduces f to g
    (hσ : Continuous σ) -- in full to talk about the witnesses
    (hτ : ContinuousOn τ (Set.range (g ∘ σ)))
    (heq : ∀ x, f x = τ (g (σ x)))
    (A : Set X)
    (x : X) (hx :  x ∈ A)
    (hsx : (σ x) ∈ (isolatedLocus g (σ '' A)) )
    : (x ∈ isolatedLocus f A) := by
  -- 1. Unpack the hypothesis hsx.
  -- hsx is of the form `(σ x ∈ σ '' A) ∧ (∃ U, ...)`
    obtain ⟨_h_in_image, U, hU_isOpen, h_sx_in_U, h_g_const⟩ := hsx; -- U open st g is locally constant on σ '' A ∩ A

    -- 2. Define the preimage set.
    let V : Set X := σ ⁻¹' U

    -- 3. Prove V is open and contains x.
    have hV_isOpen : IsOpen V := hU_isOpen.preimage hσ
    have h_x_in_V : x ∈ V := h_sx_in_U

    -- 4. Prove f is constant on V ∩ A.
    have h_f_const : ∀ y ∈ V ∩ A, f y = f x := by
    -- Introduce an arbitrary y and the hypothesis that it's in V ∩ A
      intro y hy

      -- Extract y ∈ V and y ∈ A
      have h_sy_in_U : σ y ∈ U := hy.1
      have h_y_in_A : y ∈ A := hy.2

      -- To use h_g_const, we need to show σ y ∈ σ '' A
      have h_sy_in_image : σ y ∈ σ '' A := mem_image_of_mem σ h_y_in_A

      -- Now we can apply our knowledge about g
      have h_g_eq : g (σ y) = g (σ x) := h_g_const (σ y) ⟨h_sy_in_U, h_sy_in_image⟩

      -- Finally, use the reduction identity to prove f y = f x
      rw [heq y, heq x, h_g_eq]

    -- 5. Construct the final proof object
    exact ⟨hx, V, hV_isOpen, h_x_in_V, h_f_const⟩


/-- If `f ≤ g` and `g` is scattered, then `f` is scattered.
uses the lemma ContinuouslyReduces.scattered_local
-/
theorem ContinuouslyReduces.scattered {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (hred : f ≤ g) (hg : ScatteredFun g) :
    ScatteredFun f := by
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred;
    --obtain ⟨U, hUo, hyU, hU⟩ := hg;
    intro S hS -- let S be a nonempty subset of X
    let A : Set X' := σ '' S -- let A be the image of S by σ
    have hA_nonempty :A.Nonempty := hS.image σ -- A is non empty
    -- now we use that g is scattered
    -- Step 1: Specialize the hypothesis to your set A
    have hg_A : ∃ U, IsOpen U ∧ (U ∩ A).Nonempty ∧ ∀ x ∈ U ∩ A, ∀ x' ∈ U ∩ A, g x = g x' := hg A hA_nonempty
    -- Step 2: Unpack the specialized hypothesis
    obtain ⟨U, hU_open, hU_nonempty, hg_const⟩ := hg_A
    -- let x be a point in A with σ x = y
    obtain ⟨y, hy_in_U, hy_in_image⟩ := hU_nonempty
    -- Replace 'rfl' stands for implicit reflexivity of equality in y=σx, henceforth σx
    obtain ⟨x, hx_in_S, rfl⟩ := hy_in_image
    -- This destroys 'hy_in_image', replaces 'y' with 'σ x',
    -- and updates 'hy_in_U' to mean 'σ x ∈ U'
    -- Since hy_in_image was destroyed, we quickly recreate the proof
    -- that σ x is in A.
    have h_sx_in_A : σ x ∈ A := Set.mem_image_of_mem σ hx_in_S
    have h_g_const_ : ∀ y ∈ U ∩ A, g y = g (σ x) := by
     intro z hz
     exact hg_const z hz (σ x) ⟨hy_in_U, h_sx_in_A⟩
    have hy_in_isolatedLocus : (σ x ∈ (isolatedLocus g A)) := by exact ⟨h_sx_in_A, U, hU_open, hy_in_U, h_g_const_⟩
    have hx_in_isolatedLocus : (x ∈ isolatedLocus f S) := by
      exact ContinuouslyReduces.scattered_local σ τ hσ hτ heq S x hx_in_S hy_in_isolatedLocus
    obtain ⟨x_in_S, V, hVopen, hx_in_V, h_const_VS⟩ := hx_in_isolatedLocus
    have h_VS_nonempty : (V ∩ S).Nonempty := by exact ⟨x, hx_in_V, x_in_S⟩
    --  h_const_VS states that all points are mapped to the image of x under f
    -- what the definition of scattered requires is that any two points have the same image under f
    have hf_const_adapted : ∀ z ∈ V ∩ S, ∀ z' ∈ V ∩ S, f z = f z' := by
      intro z hz z' hz'
      -- Since f z = f x and f z' = f x, we can rewrite both to be f x
      rw [h_const_VS z hz, h_const_VS z' hz']
    exact ⟨V, hVopen, h_VS_nonempty, hf_const_adapted⟩

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

-- 4. Define your custom shorthand notation
notation "CantorRat" => CantorEventuallyZero

instance : TopologicalSpace CantorEventuallyZero := instTopologicalSpaceSubtype

/-- Helper: extract the canonical prefix of an eventually-zero sequence. -/
noncomputable def cantorRatPrefix (x : CantorEventuallyZero) : List (Fin 2) := by
  classical
  exact PiNat.res x.val (Nat.find x.prop)

/-
**Splitting lemma.** In a nowhere locally constant continuous function on a metric space
into a T₂ space, any ball contains two disjoint sub-balls with separated images.
-/
lemma nlc_splitting_lemma {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) :
    ∀ x : X, ∀ ε > 0, ∃ x' : X, ∃ ε' > 0, ε' < ε ∧
      Metric.closedBall x ε' ⊆ Metric.ball x ε ∧
      Metric.closedBall x' ε' ⊆ Metric.ball x ε ∧
      Disjoint (Metric.closedBall x ε') (Metric.closedBall x' ε') ∧
      ∃ U₀ U₁ : Set Y, IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧
        g '' (Metric.ball x ε') ⊆ U₀ ∧ g '' (Metric.ball x' ε') ⊆ U₁ := by
  exact fun x ε a => splitting_lemma_nlc hg hnlc x ε a

/-!
**Cantor scheme existence.** Given a continuous NLC function, there exist
center/radius/open-set assignments satisfying all the Cantor scheme properties.
-/
lemma cantor_scheme_exists {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) (x₀ : X) :
    ∃ (c : List (Fin 2) → X) (r : List (Fin 2) → ℝ) (U : List (Fin 2) → Set Y),
      c [] = x₀ ∧
      (∀ l, 0 < r l) ∧
      (∀ l, c (0 :: l) = c l) ∧
      (∀ l (a : Fin 2), r (a :: l) ≤ r l / 2) ∧
      (∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
        Metric.ball (c l) (r l)) ∧
      (∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                      (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) ∧
      (∀ l (a : Fin 2), IsOpen (U (a :: l))) ∧
      (∀ l, Disjoint (U (0 :: l)) (U (1 :: l))) ∧
      (∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l)) := by
  -- Define the functions c, r, U by recursion on lists using the splitting lemma.
  have h_split : ∀ x : X, ∀ ε > 0, ∃ x' : X, ∃ ε' > 0, ε' < ε ∧ Metric.closedBall x ε' ⊆ Metric.ball x ε ∧ Metric.closedBall x' ε' ⊆ Metric.ball x ε ∧ Disjoint (Metric.closedBall x ε') (Metric.closedBall x' ε') ∧ ∃ U₀ U₁ : Set Y, IsOpen U₀ ∧ IsOpen U₁ ∧ Disjoint U₀ U₁ ∧ g '' (Metric.ball x ε') ⊆ U₀ ∧ g '' (Metric.ball x' ε') ⊆ U₁ := by
    exact nlc_splitting_lemma g hg hnlc
  choose! x' ε' hε' hε'_lt hε'_closedBall hε'_closedBall' hε'_disjoint hU₀ hU₁ hU₀_open hU₁_open hU₀_disjoint hU₀_image hU₁_image using h_split;
  -- Define the functions c, r, U by recursion on lists using the splitting lemma and the chosen functions x', ε', hU₀, hU₁.
  have h_rec : ∃ (F : List (Fin 2) → X × ℝ × Set Y), F [] = (x₀, 1, Set.univ) ∧ (∀ l, 0 < (F l).2.1) ∧ (∀ l, (F (0 :: l)).1 = (F l).1) ∧ (∀ l, (F (1 :: l)).1 = x' (F l).1 (F l).2.1) ∧ (∀ l, (F (0 :: l)).2.1 = min ((F l).2.1 / 2) (ε' (F l).1 (F l).2.1)) ∧ (∀ l, (F (1 :: l)).2.1 = min ((F l).2.1 / 2) (ε' (F l).1 (F l).2.1)) ∧ (∀ l, (F (0 :: l)).2.2 = hU₀ (F l).1 (F l).2.1) ∧ (∀ l, (F (1 :: l)).2.2 = hU₁ (F l).1 (F l).2.1) := by
    refine' ⟨ fun l => List.foldr ( fun a p => if a = 0 then ( p.1, min ( p.2.1 / 2 ) ( ε' p.1 p.2.1 ), hU₀ p.1 p.2.1 ) else ( x' p.1 p.2.1, min ( p.2.1 / 2 ) ( ε' p.1 p.2.1 ), hU₁ p.1 p.2.1 ) ) ( x₀, 1, Set.univ ) l, _, _, _, _, _, _ ⟩ <;> simp +decide;
    intro l; induction l <;> simp +decide [ * ] ;
    split_ifs <;> simp +decide [ *, lt_min_iff ];
  obtain ⟨ F, hF₁, hF₂, hF₃, hF₄, hF₅, hF₆, hF₇, hF₈ ⟩ := h_rec; use fun l => F l |>.1, fun l => F l |>.2.1, fun l => F l |>.2.2; simp_all +decide [ Fin.forall_fin_two ] ;
  refine' ⟨ _, _, _ ⟩;
  · intro l; exact ⟨by
    exact Metric.closedBall_subset_ball ( lt_of_le_of_lt ( min_le_left _ _ ) ( half_lt_self ( hF₂ l ) ) ), by
      exact Set.Subset.trans ( Metric.closedBall_subset_closedBall ( min_le_right _ _ ) ) ( hε'_closedBall' _ _ ( hF₂ _ ) )⟩;
  · intro l; specialize hε'_disjoint ( F l |>.1 ) ( F l |>.2.1 ) ( hF₂ l ) ; simp_all +decide [ Set.disjoint_left ] ;
  · intro l; specialize hU₀_image ( F l |>.1 ) ( F l |>.2.1 ) ( hF₂ l ) ; specialize hU₁_image ( F l |>.1 ) ( F l |>.2.1 ) ( hF₂ l ) ; simp_all +decide [ Set.subset_def ] ;

/-
Centers are nested: any descendant's center lies in the ancestor's closed ball.
-/
lemma scheme_center_in_closedBall {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l)) :
    ∀ (l₁ l₂ : List (Fin 2)), c (l₁ ++ l₂) ∈ Metric.closedBall (c l₂) (r l₂) := by
  intro l₁ l₂;
  induction' l₁ with a l₁ ih;
  · exact Metric.mem_closedBall_self ( le_of_lt ( hr_pos _ ) );
  · have h_center : ∀ l₁ l₂, Metric.closedBall (c (l₁ ++ l₂)) (r (l₁ ++ l₂)) ⊆ Metric.closedBall (c l₂) (r l₂) := by
      intro l₁ l₂; induction' l₁ with a l₁ ih generalizing l₂; aesop;
      exact Set.Subset.trans ( hball _ _ ) ( Metric.ball_subset_closedBall.trans ( ih _ ) );
    exact h_center ( a :: l₁ ) l₂ ( Metric.mem_closedBall_self ( hr_pos _ |> le_of_lt ) )

/-
Radius bound: the radius at depth n is at most r([]) / 2^n.
-/
lemma scheme_radius_bound {r : List (Fin 2) → ℝ}
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2) :
    ∀ (l : List (Fin 2)), r l ≤ r [] / 2 ^ l.length := by
  intro l
  induction' l with l ih;
  · norm_num;
  · simpa only [ pow_succ', div_div, List.length_cons ] using le_trans ( hr_half _ _ ) ( by ring_nf at *; linarith )

/-
Two list prefixes (in Cantor scheme convention) that diverge give centers
in disjoint closed balls. This implies injectivity of the center map.
-/
lemma scheme_disjoint_of_ne {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l))))
    {l₁ l₂ : List (Fin 2)} (hne : l₁ ≠ l₂) (hlen : l₁.length = l₂.length) :
    c l₁ ≠ c l₂ := by
  -- By induction on the length of the lists, we can show that for any two different lists of the same length, their corresponding closed balls are disjoint.
  have h_ind : ∀ n : ℕ, ∀ (l₁ l₂ : List (Fin 2)), l₁.length = n → l₂.length = n → l₁ ≠ l₂ → Disjoint (Metric.closedBall (c l₁) (r l₁)) (Metric.closedBall (c l₂) (r l₂)) := by
    intro n
    induction' n with n ih;
    · aesop;
    · intro l₁ l₂ hl₁ hl₂ hne
      obtain ⟨a₁, l₁', rfl⟩ : ∃ a₁ l₁', l₁ = a₁ :: l₁' := by
        exact List.exists_cons_of_ne_nil ( by rintro rfl; contradiction )
      obtain ⟨a₂, l₂', rfl⟩ : ∃ a₂ l₂', l₂ = a₂ :: l₂' := by
        exact List.exists_cons_of_ne_nil ( by rintro rfl; contradiction );
      by_cases h : l₁' = l₂' <;> simp_all +decide [ Set.disjoint_left ];
      · fin_cases a₁ <;> fin_cases a₂ <;> simp_all +decide;
        intro a ha; specialize hdisj l₂'; contrapose! hdisj; aesop;
      · intro x hx; specialize ih l₁' l₂' hl₁ hl₂ h; fin_cases a₁ <;> fin_cases a₂ <;> simp_all +decide ;
        · contrapose! ih;
          exact ⟨ x, hball l₁' |>.1 hx |> fun h => by simpa using h.le, hball l₂' |>.1 ih |> fun h => by simpa using h.le ⟩;
        · contrapose! ih;
          exact ⟨ x, hball _ |>.1 hx |> Metric.mem_ball.mp |> le_of_lt, hball _ |>.2 ih |> Metric.mem_ball.mp |> le_of_lt ⟩;
        · contrapose! ih;
          exact ⟨ x, hball _ |>.2 hx |> fun h => by simpa using h.le, hball _ |>.1 ih |> fun h => by simpa using h.le ⟩;
        · contrapose! ih;
          exact ⟨ x, hball _ |>.2 hx |> fun h => by simpa using h.le, hball _ |>.2 ih |> fun h => by simpa using h.le ⟩;
  exact fun h => Set.disjoint_left.mp ( h_ind _ _ _ hlen rfl hne ) ( Metric.mem_closedBall_self ( le_of_lt ( hr_pos _ ) ) ) ( h.symm ▸ Metric.mem_closedBall_self ( le_of_lt ( hr_pos _ ) ) )

/-
Prepending zeros to a list doesn't change the center.
-/
lemma scheme_center_replicate_zero {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X}
    (hc_zero : ∀ l, c (0 :: l) = c l) :
    ∀ (n : ℕ) (l : List (Fin 2)), c (List.replicate n 0 ++ l) = c l := by
  intro n l; induction' n with n ih generalizing l <;> simp_all +decide [ List.replicate ] ;

/-
cantorRatPrefix has length Nat.find x.prop.
-/
lemma cantorRatPrefix_length (x : CantorEventuallyZero) :
    (cantorRatPrefix x).length = @Nat.find _ (Classical.decPred _) x.prop := by
  convert PiNat.res_length x.val ( Nat.find x.prop )

/-
For n ≥ Nat.find, x.val n = 0.
-/
lemma cantorRat_zero_beyond (x : CantorEventuallyZero) (n : ℕ)
    (hn : n ≥ @Nat.find _ (Classical.decPred _) x.prop) : x.val n = 0 := by
  grind

/-
Extending PiNat.res beyond the prefix length just prepends zeros.
-/
lemma res_extends_prefix (x : CantorEventuallyZero) (n : ℕ)
    (hn : n ≥ @Nat.find _ (Classical.decPred _) x.prop) :
    PiNat.res x.val n = List.replicate (n - @Nat.find _ (Classical.decPred _) x.prop) 0 ++ cantorRatPrefix x := by
  induction' n with n ih;
  · unfold cantorRatPrefix;
    grind +suggestions;
  · by_cases h : n ≥ Nat.find x.prop;
    · rw [ Nat.succ_sub h, PiNat.res ];
      grind;
    · cases hn.eq_or_lt <;> simp_all +decide [ Nat.sub_eq_zero_of_le, PiNat.res ];
      · unfold cantorRatPrefix;
        simp +decide [ *, PiNat.res ];
      · grind

/-
The center at PiNat.res x.val n equals the center at cantorRatPrefix x for n ≥ prefix length.
-/
lemma center_of_extended_res {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} (hc_zero : ∀ l, c (0 :: l) = c l)
    (x : CantorEventuallyZero) (n : ℕ)
    (hn : n ≥ @Nat.find _ (Classical.decPred _) x.prop) :
    c (PiNat.res x.val n) = c (cantorRatPrefix x) := by
  convert scheme_center_replicate_zero hc_zero ( n - Nat.find x.prop ) ( cantorRatPrefix x ) using 1;
  rw [ res_extends_prefix x n hn ]

/-
The σ map is injective: different CantorRat elements give different centers.
-/
lemma cantor_sigma_injective {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) :
    Function.Injective (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
  intro x y hxy
  have h_prefix_eq : PiNat.res x.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length) = PiNat.res y.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length) := by
    have h_prefix_eq : c (PiNat.res x.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length)) = c (PiNat.res y.val (max (cantorRatPrefix x).length (cantorRatPrefix y).length)) := by
      convert hxy using 1;
      · apply center_of_extended_res hc_zero x (max (cantorRatPrefix x).length (cantorRatPrefix y).length);
        exact le_max_of_le_left ( by rw [ cantorRatPrefix_length ] );
      · apply center_of_extended_res hc_zero y (max (cantorRatPrefix x).length (cantorRatPrefix y).length) (by
        exact le_max_of_le_right ( by rw [ cantorRatPrefix_length ] ));
    have := @scheme_disjoint_of_ne X _ c r hr_pos hball hdisj ( PiNat.res x.val ( max ( cantorRatPrefix x ).length ( cantorRatPrefix y ).length ) ) ( PiNat.res y.val ( max ( cantorRatPrefix x ).length ( cantorRatPrefix y ).length ) ) ; simp_all +decide ;
  refine' Subtype.ext _;
  grind +suggestions

/-
σ(x) is always in the closed ball at any truncation level n.
-/
lemma sigma_in_closedBall_res {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (x : CantorEventuallyZero) (n : ℕ) :
    c (cantorRatPrefix x) ∈ Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
  by_cases h : n ≤ Nat.find x.prop;
  · -- Since cantorRatPrefix x is the prefix of x up to the point where it becomes zero, and n ≤ Nat.find x.prop, we can write cantorRatPrefix x as l₁ ++ PiNat.res x.val n for some l₁.
    obtain ⟨l₁, hl₁⟩ : ∃ l₁ : List (Fin 2), cantorRatPrefix x = l₁ ++ PiNat.res x.val n := by
      have h_decomp : ∀ m n : ℕ, m ≤ n → ∃ l₁ : List (Fin 2), PiNat.res x.val n = l₁ ++ PiNat.res x.val m := by
        intro m n hmn
        induction' hmn with n hn ih;
        · exact ⟨ [ ], rfl ⟩;
        · obtain ⟨ l₁, hl₁ ⟩ := ih; use x.val n :: l₁; simp +decide [ hl₁ ] ;
      exact h_decomp _ _ h;
    convert scheme_center_in_closedBall hr_pos hball l₁ ( PiNat.res x.val n ) using 1;
    rw [hl₁];
  · have h_center_eq : c (PiNat.res x.val n) = c (cantorRatPrefix x) := by
      apply center_of_extended_res hc_zero x n (le_of_not_ge h);
    simp +decide [ h_center_eq, hr_pos ];
    exact le_of_lt ( hr_pos _ )

/-
The σ map is continuous from CantorRat to X.
-/
lemma cantor_sigma_continuous {X : Type*} [MetricSpace X]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l)) :
    Continuous (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
  refine' continuous_iff_continuousAt.mpr _;
  intro x;
  refine' Metric.tendsto_nhds.mpr _;
  intro ε εpos
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * r (PiNat.res x.val n) < ε := by
    -- Since $r(PiNat.res x.val n) \leq r([]) / 2^n$, we can choose $n$ such that $2 * r([]) / 2^n < \epsilon$.
    have h_bound : ∃ n : ℕ, 2 * r [] / 2 ^ n < ε := by
      simpa using tendsto_const_nhds.div_atTop ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) |> fun h => h.eventually ( gt_mem_nhds εpos ) |> fun h => h.exists;
    obtain ⟨ n, hn ⟩ := h_bound;
    refine' ⟨ n, lt_of_le_of_lt _ hn ⟩;
    convert mul_le_mul_of_nonneg_left ( scheme_radius_bound hr_half ( PiNat.res x.val n ) ) zero_le_two using 1 ; ring;
    simp +decide [ PiNat.res ]
  have h_open : IsOpen {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} := by
    have h_open : IsOpen (PiNat.cylinder x.val n) := by
      grind +suggestions;
    convert h_open.preimage _ using 1;
    rotate_left;
    use fun y => y.val;
    · exact continuous_subtype_val;
    · grind +suggestions
  have h_cont : ∀ y : CantorEventuallyZero, PiNat.res y.val n = PiNat.res x.val n → dist (c (cantorRatPrefix y)) (c (cantorRatPrefix x)) < ε := by
    intro y hy
    have h_dist : dist (c (cantorRatPrefix y)) (c (cantorRatPrefix x)) ≤ 2 * r (PiNat.res x.val n) := by
      have h_dist : c (cantorRatPrefix y) ∈ Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) ∧ c (cantorRatPrefix x) ∈ Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
        exact ⟨ by simpa only [ hy ] using sigma_in_closedBall_res hr_pos hc_zero hball y n, by simpa only [ hy ] using sigma_in_closedBall_res hr_pos hc_zero hball x n ⟩;
      exact le_trans ( dist_triangle_right _ _ _ ) ( by linarith [ Metric.mem_closedBall.mp h_dist.1, Metric.mem_closedBall.mp h_dist.2 ] )
    linarith [h_dist]
  exact Filter.mem_of_superset (IsOpen.mem_nhds h_open (by
  rfl)) (by
  exact fun y hy => h_cont y hy)

/-
The embedding property of σ : CantorRat → X.
Given a Cantor scheme with the standard properties, the map
σ(x) = c(cantorRatPrefix x) is a topological embedding.
-/
lemma cantor_sigma_isEmbedding {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g)
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l)))) :
    Topology.IsEmbedding (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
  have h_embedding : Function.Injective (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) ∧ Continuous (fun x : CantorEventuallyZero => c (cantorRatPrefix x)) := by
    exact ⟨ cantor_sigma_injective hr_pos hc_zero hball hdisj, cantor_sigma_continuous hr_pos hc_zero hr_half hball ⟩;
  have h_embedding : ∀ x : CantorEventuallyZero, ∀ n : ℕ, ∃ V ∈ nhds (c (cantorRatPrefix x)), ∀ y : CantorEventuallyZero, c (cantorRatPrefix y) ∈ V → PiNat.res y.val n = PiNat.res x.val n := by
    intro x n
    use Metric.ball (c (PiNat.res x.val n)) (r (PiNat.res x.val n));
    refine' ⟨ Metric.isOpen_ball.mem_nhds _, _ ⟩;
    · by_cases hN : @Nat.find _ (Classical.decPred _) x.prop ≤ n;
      · have h_sigma_in_closedBall_res : c (cantorRatPrefix x) = c (PiNat.res x.val n) := by
          apply Eq.symm; exact (by
            have := center_of_extended_res hc_zero x n hN;
            exact this
          );
        aesop;
      · have h_closedBall_subset_ball : Metric.closedBall (c (cantorRatPrefix x)) (r (cantorRatPrefix x)) ⊆ Metric.ball (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
          have h_closedBall_subset_ball : ∀ k ≥ n + 1, Metric.closedBall (c (PiNat.res x.val k)) (r (PiNat.res x.val k)) ⊆ Metric.ball (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) := by
            intro k hk
            induction' hk with k hk ih;
            · convert hball ( PiNat.res x.val n ) ( x.val n ) using 1;
            · refine' Set.Subset.trans _ ih;
              convert hball ( PiNat.res x.val k ) ( x.val k ) |> Set.Subset.trans <| Metric.ball_subset_closedBall using 1;
          convert h_closedBall_subset_ball ( Nat.find x.prop ) ( by linarith ) using 1;
        exact h_closedBall_subset_ball ( Metric.mem_closedBall_self ( le_of_lt ( hr_pos _ ) ) );
    · intro y hy
      by_contra h_neq
      obtain ⟨k, hk⟩ : ∃ k < n, PiNat.res y.val (k + 1) ≠ PiNat.res x.val (k + 1) ∧ ∀ j < k, PiNat.res y.val (j + 1) = PiNat.res x.val (j + 1) := by
        have h_exists_k : ∃ k < n, PiNat.res y.val (k + 1) ≠ PiNat.res x.val (k + 1) := by
          exact ⟨ n - 1, Nat.pred_lt ( by aesop ), by cases n <;> aesop ⟩
        generalize_proofs at *; (
        exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => Classical.not_not.1 fun h => Nat.find_min h_exists_k hj ⟨ by linarith [ Nat.find_spec h_exists_k |>.1 ], h ⟩ ⟩)
      generalize_proofs at *; (
      -- Since $c(cantorRatPrefix y) \in Metric.ball(c(res x n), r(res x n))$, we have $c(cantorRatPrefix y) \in Metric.closedBall(c(res x (k+1)), r(res x (k+1)))$.
      have h_closedBall : c (cantorRatPrefix y) ∈ Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1))) := by
        have h_closedBall : Metric.closedBall (c (PiNat.res x.val n)) (r (PiNat.res x.val n)) ⊆ Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1))) := by
          have h_closedBall : ∀ m ≥ k + 1, Metric.closedBall (c (PiNat.res x.val m)) (r (PiNat.res x.val m)) ⊆ Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1))) := by
            intro m hm
            induction' hm with m hm ih
            generalize_proofs at *; (
            exact Set.Subset.rfl);
            refine' Set.Subset.trans _ ih
            generalize_proofs at *; (
            have := hball ( PiNat.res x.val m ) ( x.val m ) ; simp_all +decide [ PiNat.res ] ;
            exact Set.Subset.trans this ( Metric.ball_subset_closedBall ))
          generalize_proofs at *; (
          exact h_closedBall n ( by linarith ))
        generalize_proofs at *; (
        exact h_closedBall <| Metric.ball_subset_closedBall hy)
      generalize_proofs at *; (
      have h_closedBall_y : c (cantorRatPrefix y) ∈ Metric.closedBall (c (PiNat.res y.val (k + 1))) (r (PiNat.res y.val (k + 1))) := by
        apply sigma_in_closedBall_res;
        · exact hr_pos;
        · exact hc_zero;
        · exact hball
      generalize_proofs at *; (
      have h_disjoint : Disjoint (Metric.closedBall (c (PiNat.res y.val (k + 1))) (r (PiNat.res y.val (k + 1)))) (Metric.closedBall (c (PiNat.res x.val (k + 1))) (r (PiNat.res x.val (k + 1)))) := by
        have h_disjoint : ∀ l : List (Fin 2), ∀ a b : Fin 2, a ≠ b → Disjoint (Metric.closedBall (c (a :: l)) (r (a :: l))) (Metric.closedBall (c (b :: l)) (r (b :: l))) := by
          intro l a b hab; fin_cases a <;> fin_cases b <;> simp_all +decide ;
          exact Disjoint.symm ( hdisj l )
        generalize_proofs at *; (
        convert h_disjoint ( PiNat.res ( y.val ) k ) ( y.val k ) ( x.val k ) _ using 1 <;> simp_all +decide [ PiNat.res ];
        · grind +suggestions;
        · grind +suggestions)
      generalize_proofs at *; (
      exact h_disjoint.le_bot ⟨ h_closedBall_y, h_closedBall ⟩))));
  have h_embedding : ∀ x : CantorEventuallyZero, ∀ U ∈ nhds x, ∃ V ∈ nhds (c (cantorRatPrefix x)), ∀ y : CantorEventuallyZero, c (cantorRatPrefix y) ∈ V → y ∈ U := by
    intro x U hU
    obtain ⟨n, hn⟩ : ∃ n : ℕ, {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} ⊆ U := by
      rw [ mem_nhds_iff ] at hU;
      obtain ⟨ t, ht₁, ht₂, ht₃ ⟩ := hU;
      rcases ht₂ with ⟨ s, hs₁, rfl ⟩;
      rw [ isOpen_pi_iff ] at hs₁;
      obtain ⟨ I, u, hu₁, hu₂ ⟩ := hs₁ _ ht₃;
      use I.sup id + 1;
      intro y hy;
      refine' ht₁ _;
      grind +suggestions;
    exact Exists.elim ( h_embedding x n ) fun V hV => ⟨ V, hV.1, fun y hy => hn ( hV.2 y hy ) ⟩;
  refine' ⟨ _, _ ⟩;
  · refine' Topology.isInducing_iff_nhds.2 fun x => _;
    refine' le_antisymm _ _;
    · exact Filter.tendsto_iff_comap.mp ( ‹ ( Injective fun x => c ( cantorRatPrefix x ) ) ∧ Continuous fun x => c ( cantorRatPrefix x ) ›.2.tendsto x );
    · intro U hU;
      rcases h_embedding x U hU with ⟨ V, hV, hV' ⟩ ; exact ⟨ V, hV, fun y hy => hV' y hy ⟩;
  · exact And.left ‹_›

/-
g(σ(x)) is in the open set U at level n+1 when σ(x) is in the corresponding ball.
-/
lemma g_sigma_in_U {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    {U : List (Fin 2) → Set Y} (g : X → Y)
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l))
    (x : CantorEventuallyZero) (n : ℕ) :
    g (c (cantorRatPrefix x)) ∈ U (PiNat.res x.val (n + 1)) := by
  by_cases h : @Nat.find _ (Classical.decPred _) x.prop ≤ n + 1;
  · have := center_of_extended_res hc_zero x ( n + 1 ) h;
    rw [ ← this ];
    convert hU_img ( PiNat.res x.val n ) ( x.val n ) ( Set.mem_image_of_mem _ _ ) using 1;
    convert Metric.mem_ball_self ( hr_pos _ ) using 1;
  · have h_closed_ball : c (cantorRatPrefix x) ∈ Metric.closedBall (c (PiNat.res x.val (n + 1 + 1))) (r (PiNat.res x.val (n + 1 + 1))) := by
      apply sigma_in_closedBall_res;
      · exact hr_pos;
      · exact hc_zero;
      · exact hball;
    grind +suggestions

/-
The embedding property of g ∘ σ : CantorRat → Y.
-/
lemma cantor_g_sigma_isEmbedding {X Y : Type*}
    [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    {c : List (Fin 2) → X} {r : List (Fin 2) → ℝ}
    {U : List (Fin 2) → Set Y}
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g)
    (hr_pos : ∀ l, 0 < r l)
    (hc_zero : ∀ l, c (0 :: l) = c l)
    (hr_half : ∀ l (a : Fin 2), r (a :: l) ≤ r l / 2)
    (hball : ∀ l (a : Fin 2), Metric.closedBall (c (a :: l)) (r (a :: l)) ⊆
      Metric.ball (c l) (r l))
    (hdisj : ∀ l, Disjoint (Metric.closedBall (c (0 :: l)) (r (0 :: l)))
                            (Metric.closedBall (c (1 :: l)) (r (1 :: l))))
    (hU_open : ∀ l (a : Fin 2), IsOpen (U (a :: l)))
    (hU_disj : ∀ l, Disjoint (U (0 :: l)) (U (1 :: l)))
    (hU_img : ∀ l (a : Fin 2), g '' Metric.ball (c (a :: l)) (r (a :: l)) ⊆ U (a :: l)) :
    Topology.IsEmbedding (fun x : CantorEventuallyZero => g (c (cantorRatPrefix x))) := by
  have h_subspace : Continuous (fun x : CantorEventuallyZero => g (c (cantorRatPrefix x))) := by
    exact hg.comp ( cantor_sigma_continuous hr_pos hc_zero hr_half hball );
  have h_injective : Function.Injective (fun x : CantorEventuallyZero => g (c (cantorRatPrefix x))) := by
    intro x y hxy
    by_contra hneq
    obtain ⟨k, hk⟩ : ∃ k, (PiNat.res x.val k) = (PiNat.res y.val k) ∧ x.val k ≠ y.val k := by
      obtain ⟨k, hk⟩ : ∃ k, (PiNat.res x.val k) ≠ (PiNat.res y.val k) ∧ ∀ j < k, (PiNat.res x.val j) = (PiNat.res y.val j) := by
        have h_exists_k : ∃ k, (PiNat.res x.val k) ≠ (PiNat.res y.val k) := by
          contrapose! hneq
          generalize_proofs at *;
          exact Subtype.ext ( funext fun n => by have := hneq ( n + 1 ) ; have := hneq n; simp_all +decide [ PiNat.res ] )
        generalize_proofs at *;
        exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k, fun j hj => by simpa using Nat.find_min h_exists_k hj ⟩
      generalize_proofs at *;
      rcases k <;> simp_all +decide [ PiNat.res ];
      grind
    generalize_proofs at *;
    have h_contradiction : g (c (cantorRatPrefix x)) ∈ U (PiNat.res x.val (k + 1)) ∧ g (c (cantorRatPrefix y)) ∈ U (PiNat.res y.val (k + 1)) := by
      exact ⟨ g_sigma_in_U g hr_pos hc_zero hball hU_img x k, g_sigma_in_U g hr_pos hc_zero hball hU_img y k ⟩
    generalize_proofs at *; exact (by
    cases Fin.exists_fin_two.mp ⟨ x.val k, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ y.val k, rfl ⟩ <;> simp_all +decide [ PiNat.res ];
    · exact Set.disjoint_left.mp ( hU_disj _ ) h_contradiction.1 h_contradiction.2;
    · exact Set.disjoint_left.mp ( hU_disj _ ) h_contradiction.2 h_contradiction.1);
  refine' ⟨ _, _ ⟩;
  · refine' Topology.isInducing_iff_nhds.2 fun x => le_antisymm _ _;
    · exact h_subspace.tendsto x |> fun h => h.le_comap;
    · intro s hs;
      -- Since $s$ is a neighborhood of $x$, there exists an $n$ such that the cylinder set $\{y \mid \text{res } y n = \text{res } x n\}$ is contained in $s$.
      obtain ⟨n, hn⟩ : ∃ n : ℕ, {y : CantorEventuallyZero | PiNat.res y.val n = PiNat.res x.val n} ⊆ s := by
        rw [ mem_nhds_subtype ] at hs;
        rcases hs with ⟨ u, hu, hs ⟩;
        rw [ mem_nhds_iff ] at hu;
        rcases hu with ⟨ t, ht₁, ht₂, ht₃ ⟩;
        rw [ isOpen_pi_iff ] at ht₂;
        obtain ⟨ I, u, hu₁, hu₂ ⟩ := ht₂ _ ht₃;
        use I.sup id + 1;
        intro y hy;
        refine' hs ( ht₁ ( hu₂ _ ) );
        grind +suggestions;
      refine' ⟨ ⋂ k ∈ Finset.range n, U ( PiNat.res x.val ( k + 1 ) ), _, _ ⟩;
      · refine' IsOpen.mem_nhds _ _;
        · refine' isOpen_biInter_finset fun k hk => _;
          convert hU_open ( PiNat.res x.val k ) ( x.val k ) using 1;
        · exact Set.mem_iInter₂.2 fun k hk => g_sigma_in_U g hr_pos hc_zero hball hU_img x k;
      · intro y hy; contrapose! hy; simp_all +decide [ Set.subset_def ] ;
        -- Since $y \notin s$, there exists some $k < n$ such that $y.val k \neq x.val k$.
        obtain ⟨k, hk₁, hk₂⟩ : ∃ k < n, y.val k ≠ x.val k ∧ ∀ j < k, y.val j = x.val j := by
          have h_exists_k : ∃ k < n, y.val k ≠ x.val k := by
            grind +suggestions;
          exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => Classical.not_not.1 fun h => Nat.find_min h_exists_k hj ⟨ by linarith [ Nat.find_spec h_exists_k |>.1 ], h ⟩ ⟩;
        refine' ⟨ k, hk₁, _ ⟩;
        have h_g_sigma_in_U : g (c (cantorRatPrefix y)) ∈ U (PiNat.res y.val (k + 1)) := by
          apply g_sigma_in_U;
          exact hr_pos;
          · exact hc_zero;
          · intro l a; specialize hball l; fin_cases a <;> simp_all +decide [ Metric.closedBall, Metric.ball ] ;
          · intro l a; specialize hU_img l; fin_cases a <;> simp_all +decide [ Set.image_subset_iff ] ;
            · exact fun x hx => hU_img.1 x hx;
            · exact fun x hx => hU_img.2 x <| by simpa using hx;
        have h_g_sigma_in_U : PiNat.res y.val (k + 1) = y.val k :: PiNat.res x.val k := by
          grind +suggestions;
        cases Fin.exists_fin_two.mp ⟨ y.val k, rfl ⟩ <;> cases Fin.exists_fin_two.mp ⟨ x.val k, rfl ⟩ <;> simp_all +decide [ Set.disjoint_left ];
        exact fun h => hU_disj _ h ‹_›;
  · exact h_injective

/-- The map σ : CantorRat → X defined by σ(x) = c(prefix(x)) is an embedding,
and g ∘ σ is also an embedding, given the Cantor scheme properties. -/
lemma nlc_countable_embedding_concrete {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) [Nonempty X] :
    ∃ (σ : CantorRat → X), Topology.IsEmbedding σ ∧ Topology.IsEmbedding (g ∘ σ) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  obtain ⟨x₀⟩ := id ‹Nonempty X›
  obtain ⟨c, r, U, _, hr_pos, hc_zero, hr_half, hball, hdisj, hU_open, hU_disj, hU_img⟩ :=
    cantor_scheme_exists g hg hnlc x₀
  let σ : CantorRat → X := fun x => c (cantorRatPrefix x)
  refine ⟨σ, ?_, ?_⟩
  · exact cantor_sigma_isEmbedding g hg hnlc hr_pos hc_zero hr_half hball hdisj
  · exact cantor_g_sigma_isEmbedding (U := U) g hg hnlc hr_pos hc_zero hr_half hball hdisj
      hU_open hU_disj hU_img

/-
**Cantor scheme construction.** If `g : X → Y` is continuous and NLC from a
nonempty metrizable space to a T₂ space, then there exists a countable nonempty
subset `S ⊆ X` such that:
- `S` has no isolated points (in the subspace topology)
- The restriction of `g` to `S` is a topological embedding into `Y`
-/
lemma nlc_countable_embedding {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (g : X → Y) (hg : Continuous g) (hnlc : NowhereLocllyConstant g) [Nonempty X] :
    ∃ (S : Set X), S.Countable ∧ S.Nonempty ∧
      (∀ x : S, ¬ IsOpen ({x} : Set S)) ∧
      Topology.IsEmbedding (fun (x : S) => g x.val) := by
  obtain ⟨ σ, hσ₁, hσ₂ ⟩ := nlc_countable_embedding_concrete g hg hnlc;
  refine' ⟨ Set.range σ, _, _, _, _ ⟩;
  · convert Set.countable_range σ;
    have h_countable : Set.Countable (⋃ N : ℕ, {x : ℕ → Fin 2 | ∀ n ≥ N, x n = 0}) := by
      refine' Set.countable_iUnion fun N => _;
      refine' Set.Countable.mono _ ( Set.countable_range ( fun x : Fin N → Fin 2 => fun n => if h : n < N then x ⟨ n, h ⟩ else 0 ) );
      intro x hx; use fun n => x n; ext n; aesop;
    exact h_countable.mono fun x hx => by aesop;
  · exact ⟨ _, ⟨ ⟨ fun _ => 0, ⟨ 0, fun _ _ => rfl ⟩ ⟩, rfl ⟩ ⟩;
  · intro x hx;
    -- Since CantorRat has no isolated points, the image of CantorRat under σ also has no isolated points.
    have h_no_isolated : ∀ x : CantorEventuallyZero, ¬IsOpen ({x} : Set CantorEventuallyZero) := by
      intro x hx
      have h_no_isolated : ∀ x : CantorEventuallyZero, ¬IsOpen ({x} : Set CantorEventuallyZero) := by
        intro x hx
        have h_seq : ∃ seq : ℕ → CantorEventuallyZero, Filter.Tendsto seq Filter.atTop (nhds x) ∧ ∀ n, seq n ≠ x := by
          obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, x.val n = 0 := by
            exact x.2;
          refine' ⟨ fun n => ⟨ fun i => if i = N + n + 1 then 1 else x.val i, _ ⟩, _, _ ⟩ <;> simp_all +decide [ funext_iff ];
          use N + n + 2;
          grind;
          · rw [ tendsto_subtype_rng ];
            rw [ tendsto_pi_nhds ];
            intro n; by_cases hn : n = N + n + 1 <;> simp_all +decide [ Nat.ne_of_lt ] ;
            exact ⟨ n + 1, by intros; linarith ⟩;
          · intro n hn; have := congr_arg ( fun f => f.val ( N + n + 1 ) ) hn; simp +decide [ hN ] at this;
            rw [ hN _ ( by linarith ) ] at this ; contradiction
        obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq;
        exact absurd ( hseq₁.eventually ( hx.mem_nhds rfl ) ) fun h => by obtain ⟨ n, hn ⟩ := h.exists; exact hseq₂ n hn;
      exact h_no_isolated x hx;
    obtain ⟨ y, hy ⟩ := x.2;
    have h_preimage : IsOpen (σ ⁻¹' {↑x}) := by
      convert hx.preimage ( show Continuous ( fun z : CantorEventuallyZero => ⟨ σ z, Set.mem_range_self z ⟩ ) from hσ₁.continuous.subtype_mk _ ) using 1;
      grind;
    exact h_no_isolated y ( by simpa [ show σ ⁻¹' { ( x : X ) } = { y } from Set.eq_singleton_iff_unique_mem.mpr ⟨ by aesop, fun z hz => hσ₁.injective <| by aesop ⟩ ] using h_preimage );
  · rw [ Topology.isEmbedding_iff ] at *;
    constructor;
    · rw [ Topology.isInducing_iff_nhds ] at *;
      simp +decide [ ← hσ₂.1, Filter.comap_comap ];
      intro a x hx; specialize hσ₂; have := hσ₂.1 x; simp_all +decide [ Filter.ext_iff ] ;
      intro s; specialize this ( σ ⁻¹' ( Subtype.val '' s ) ) ; simp_all +decide [ Set.subset_def ] ;
      rw [ mem_nhds_subtype ];
      grind;
    · intro x y hxy;
      rcases x with ⟨ x, ⟨ x', rfl ⟩ ⟩ ; rcases y with ⟨ y, ⟨ y', rfl ⟩ ⟩ ; have := hσ₂.2 ( by aesop : g ( σ x' ) = g ( σ y' ) ) ; aesop;

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

section ZeroDimAndDisjointUnion

/-!
## Proposition 2.14 (0dimanddisjointunion)

Let `f` be a function with separable metrizable 0-dimensional domain and `F` a class
of functions. Then `f` is locally `F` if and only if `f = ⨆ᵢ fᵢ` for some sequence of
functions `(fᵢ) ⊆ F`.

**Locally F** means: for every `x ∈ dom(f)`, there exists a clopen neighborhood `C ∋ x`
such that `f|_C ∈ F`.
-/

/-- A function `f : X → Y` is *locally in class `F`* if every point of `X` has a
clopen neighborhood on which `f` restricted is in `F`.
Here `F` is a predicate on functions from subtypes of `X` to `Y`. -/
def IsLocallyInClass {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (F : (S : Set X) → (S → Y) → Prop) : Prop :=
  ∀ x : X, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ F C (fun a => f a.val)

/-!
### Proposition 2.14 (0dimanddisjointunion)

For a function `f` with domain a subspace of the Baire space and `F` a class of
functions, `f` is locally `F` if and only if `f` is a disjoint union of functions
in `F` over a clopen partition.

The forward direction is the interesting one: in a 0-dimensional separable metrizable
space, every open cover can be refined to a clopen partition, using the tree structure
of the Baire space. The backward direction is trivial since each piece of a clopen
partition is itself clopen.
-/

/-- A function `f : X → Y` is a disjoint union of the sequence `(fᵢ)` over a clopen
partition `(Aᵢ)` of `X`. (Duplicated from Gluing.lean to avoid circular import.) -/
def IsDisjointUnion' {X Y : Type*} [TopologicalSpace X]
    {I : Type*} (f : X → Y) (A : I → Set X) (fi : ∀ i, A i → Y) : Prop :=
  (∀ i, IsClopen (A i)) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (⋃ i, A i) = univ ∧
  (∀ i (x : A i), f x.val = fi i x)

/-
**Proposition 2.14 (0dimanddisjointunion).**
Backward direction: if `f` is a disjoint union of functions in `F`,
then `f` is locally in class `F`.
-/
theorem disjoint_union_implies_locally
    {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (F : (S : Set X) → (S → Y) → Prop)
    {I : Type*} (P : I → Set X) (fi : ∀ i, P i → Y)
    (hdu : IsDisjointUnion' f P fi)
    (hF : ∀ i, F (P i) (fi i)) :
    IsLocallyInClass f F := by
  -- For any $x \in X$, there exists $i \in I$ such that $x \in P_i$.
  have h_exists_i : ∀ x : X, ∃ i : I, x ∈ P i := by
    exact fun x => by simpa using Set.ext_iff.mp hdu.2.2.1 x;
  intro x
  obtain ⟨i, hi⟩ := h_exists_i x
  use P i;
  exact ⟨ hdu.1 i, hi, by convert hF i using 1; ext a; exact hdu.2.2.2 i a ▸ rfl ⟩

/-
**Proposition 2.14 (0dimanddisjointunion).**
Forward direction for Baire space subspaces:
if `f : A → Baire` with `A ⊆ Baire` is locally in class `F`,
then `f` is a disjoint union of functions in `F`.

Note: The proof in the original paper uses the tree structure of Baire space
and minimal prefixes. It implicitly requires `F` to be closed under restriction
to clopen subsets (captured by `hF_restrict`). This is satisfied by all standard
classes (simple, scattered with rank ≤ α, etc.).
-/
theorem locally_implies_disjoint_union_baire
    {A : Set Baire}
    (f : A → Baire)
    (F : (S : Set A) → (S → Baire) → Prop)
    (hloc : IsLocallyInClass f F)
    (hF_restrict : ∀ (C D : Set A), D ⊆ C → IsClopen D →
      F C (fun a => f a.val) → F D (fun a => f a.val)) :
    ∃ (I : Type) (P : I → Set A) (fi : ∀ i, P i → Baire),
      IsDisjointUnion' f P fi ∧ ∀ i, F (P i) (fi i) := by
  choose C hC hc using hloc;
  -- use Lindelof property to get a countable subcover
  obtain ⟨I, hI⟩ : ∃ I : Set A, Set.Countable I ∧ ⋃ x ∈ I, C x = Set.univ := by
    have h_countable_subcover : IsLindelof (Set.univ : Set A) := by
      exact isLindelof_univ
    have := h_countable_subcover.elim_countable_subcover ( fun x => C x );
    exact Exists.elim ( this ( fun x => ( hC x ).isOpen ) ( fun x _ => Set.mem_iUnion_of_mem x ( hc x |>.1 ) ) ) fun r hr => ⟨ r, hr.1, Set.Subset.antisymm ( Set.subset_univ _ ) hr.2 ⟩;
  have := hI.1.exists_eq_range;
  by_cases hI_empty : I.Nonempty;
  · obtain ⟨g, hg⟩ : ∃ g : ℕ → A, I = Set.range g := by
      exact this hI_empty;
    refine' ⟨ ℕ, fun n => disjointed ( fun n => C ( g n ) ) n, fun n => fun a => f a.val, _, _ ⟩ <;> simp_all +decide [ IsDisjointUnion' ];
    · refine' ⟨ _, _, _ ⟩;
      · exact?;
      · exact fun i j hij => disjoint_disjointed _ hij;
      · convert hI.2 using 1;
        exact?;
    · intro n;
      apply hF_restrict;
      exact disjointed_subset _ _;
      · exact disjointed_clopen _ ( fun n => hC _ _ ) _;
      · exact hc _ _ |>.2;
  · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hI_empty ];
    simp_all +decide [ IsDisjointUnion' ];
    exact ⟨ PEmpty, fun _ => ∅, by aesop ⟩

end ZeroDimAndDisjointUnion

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

/-
In the Baire space, every open set containing a point has a clopen subset
containing that point. Follows from `baire_has_clopen_basis`.
-/
lemma baire_exists_clopen_subset_of_open
    (x : Baire) (U : Set Baire) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set Baire, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨B, hB_basis, _, hB_clopen⟩ := baire_has_clopen_basis
  have hU_nhds : U ∈ nhds x := hU.mem_nhds hx
  rw [hB_basis.mem_nhds_iff] at hU_nhds
  obtain ⟨V, hV_in_B, hx_in_V, hV_sub_U⟩ := hU_nhds
  exact ⟨V, hB_clopen V hV_in_B, hx_in_V, hV_sub_U⟩

/-
In a subspace of the Baire space, every open set containing a point has a
clopen subset containing that point.
-/
lemma baire_subspace_exists_clopen_subset_of_open
    (A : Set Baire) (x : A) (U : Set A) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set A, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  rcases hU with ⟨V, hV, rfl⟩;
  obtain ⟨W, hW⟩ : ∃ W : Set Baire, IsClopen W ∧ x.val ∈ W ∧ W ⊆ V := by
    exact baire_exists_clopen_subset_of_open x.val V hV hx;
  refine' ⟨ Subtype.val ⁻¹' W, _, _, _ ⟩;
  · exact hW.1.preimage continuous_subtype_val;
  · aesop;
  · exact Set.preimage_mono hW.2.2

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

/-
For a scattered function `f : A → Y`, the stabilizing set is nonempty
(the CB levels must stabilize since `A` is `Small.{0}`).
-/
lemma cb_stabilizing_set_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) :
    {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty := by
  -- By definition of scattered, the CB level at sometimes stabilizes.
  have hCBStabilize : ∃ α, CBLevel f α = CBLevel f (Order.succ α) := by
    by_contra h
    push_neg at h
    --clauses t, 3, 0
    exact absurd ( CBLevel_strictAnti_of_ne f h ) ( by rintro ⟨ g, hg ⟩ ; exact not_injective_of_ordinal g hg );
  exact hCBStabilize

/-
For a scattered function, the CB level at CBRank is empty.
-/
lemma cbLevel_at_cbRank_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) :
    CBLevel f (CBRank f) = ∅ := by
  by_cases h_empty : (CBLevel f (CBRank f)).Nonempty;
  · have h_eq : CBLevel f (CBRank f) = CBLevel f (Order.succ (CBRank f)) := by
      exact csInf_mem ( cb_stabilizing_set_nonempty f hf );
    exact absurd h_eq ( ne_of_gt ( CBLevel_succ_ssubset_of_scattered f hf _ h_empty ) );
  · exact Set.not_nonempty_iff_eq_empty.mp h_empty

/-
The restriction of a scattered function to an open set is scattered.
-/
lemma scattered_restriction_open {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : ScatteredFun f)
    (U : Set X) (hU : IsOpen U) :
    ScatteredFun (f ∘ (Subtype.val : U → X)) := by
  intro S hS;
  obtain ⟨ x, hx ⟩ := hS;
  obtain ⟨ V, hV₁, hV₂, hV₃ ⟩ := hf ( Subtype.val '' S ) ⟨ _, Set.mem_image_of_mem _ hx ⟩;
  refine' ⟨ Subtype.val ⁻¹' V, _, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
  · exact hU.inter hV₁;
  · grind +extAll

/-
From x ∈ isolatedLocus f (CBLevel f β), get open U with f constant on
    U ∩ CBLevel f β and CBLevel f (succ β) ∩ U = ∅.
-/
lemma isolatedLocus_gives_simple_neighborhood {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (β : Ordinal.{0})
    (x : X)
    (hx : x ∈ isolatedLocus f (CBLevel f β)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      CBLevel f (Order.succ β) ∩ U = ∅ ∧
      ∀ y ∈ U ∩ CBLevel f β, f y = f x := by
  obtain ⟨U, hU_open, hx_in_U, hconst⟩ : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ (CBLevel f β), f y = f x := by
    exact hx.2;
  refine' ⟨ U, hU_open, hx_in_U, _, hconst ⟩;
  simp_all +decide [ Set.ext_iff, CBLevel_succ' ];
  intro y hy hy' hy''; contrapose! hy'; unfold isolatedLocus at *; aesop;

/-
Key lemma for decomposition: the restriction of f to a Baire-clopen set
    contained in the isolated locus neighborhood is simple.
-/
lemma restriction_to_clopen_is_simple
    {A : Set Baire}
    (f : A → Baire)
    (hf : ScatteredFun f)
    (β : Ordinal.{0})
    (V : Set Baire)
    (hV : IsClopen V)
    (hx_exists : ∃ x : A, (x : Baire) ∈ V ∧ x ∈ CBLevel f β)
    (hempty : CBLevel f (Order.succ β) ∩ (Subtype.val ⁻¹' V : Set A) = ∅)
    (hconst : ∃ y : Baire, ∀ z ∈ (Subtype.val ⁻¹' V : Set A) ∩ CBLevel f β, f z = y) :
    SimpleFun (f ∘ (Subtype.val : {a : A | (a : Baire) ∈ V} → A)) := by
  refine' ⟨ _, β, _, _, _ ⟩;
  · apply_rules [ ScatteredFun, scattered_restriction_open ];
    exact hV.isOpen.preimage continuous_subtype_val;
  · obtain ⟨ x, hx₁, hx₂ ⟩ := hx_exists; use ⟨ x, hx₁ ⟩ ; simp_all +decide [ local_cb_derivative ] ;
    have h_local : Subtype.val '' CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) β = (CBLevel f β) ∩ Subtype.val ⁻¹' V := by
      convert local_cb_derivative ( Subtype.val ⁻¹' V ) ( hV.2.preimage ( continuous_subtype_val ) ) β using 1;
      exact?;
    exact h_local.symm.subset ⟨ hx₂, hx₁ ⟩ |> fun ⟨ y, hy₁, hy₂ ⟩ => hy₂ ▸ hy₁;
  · have h_local_cb_derivative : Subtype.val '' CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) (Order.succ β) = CBLevel f (Order.succ β) ∩ Subtype.val ⁻¹' V := by
      apply local_cb_derivative;
      exact hV.isOpen.preimage continuous_subtype_val;
    aesop;
  · use hconst.choose;
    intro x hx;
    apply hconst.choose_spec;
    exact ⟨ x.2, local_cb_derivative _ ( show IsOpen ( Subtype.val ⁻¹' V ) from hV.isOpen.preimage continuous_subtype_val ) _ |>.subset ( Set.mem_image_of_mem _ hx ) |> fun h => h.1 ⟩

/-
**Decomposition Lemma.** Any scattered function from a zero-dimensional separable
metrizable space is locally simple: around each point there is a clopen neighborhood
on which `f` is simple.
The proof uses `exists_clopen_subset_of_open` (clopen basis) and the CB analysis.
commented this abstract version for a concrete one in the Baire space
theorem decomposition_lemma {X Y : Type*}
[TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
[TotallyDisconnectedSpace X]
[TopologicalSpace Y]
{f : X → Y} (hf : ScatteredFun f) :
∀ x : X, ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
SimpleFun (f ∘ (Subtype.val : U → X)) := by
sorry

Original statement (incorrect for x ∉ A since the restricted domain
may be empty, making SimpleFun false). See `decomposition_lemma_baire` below
for the corrected version.
theorem decomposition_lemma_baire_orig
(A : Set Baire)
(f: A → Baire)
(hf : ScatteredFun f) :
∀ x : Baire, ∃ U : Set Baire, IsClopen U ∧ x ∈ U ∧
SimpleFun ((f ∘ (Subtype.val : {a : A | (a : Baire) ∈ U} → A)))
:= by sorry

**Decomposition Lemma (corrected).** Any scattered function `f : A → Baire`
with `A ⊆ Baire` is locally simple: around each point of `A` there is a clopen
neighborhood (in the Baire space) on which `f` is simple.
-/
theorem decomposition_lemma_baire
    (A : Set Baire)
    (f : A → Baire)
    (hf : ScatteredFun f) :
    ∀ x : A, ∃ U : Set Baire, IsClopen U ∧ (x : Baire) ∈ U ∧
         SimpleFun ((f ∘ (Subtype.val : {a : A | (a : Baire) ∈ U} → A)))
     := by
  -- this uses the generalized reduction property (baire_open_reduction_rel)
  -- of open sets for subsets of the Baire space
  -- By induction on α = CBrank f.
  -- Vacuously true if α=0.
  --  If α is limit, then use limit_locally_lower
  -- every $x\in \dom f$ admits a clopen neighbourhood $C$ such that $\CB(f\restr{C})<\CB(f)$
  -- and the result follows by induction hypothesis and \cref{0dimanddisjointunion}.
  -- Finally, assume that $\CB(f)=\beta+1$ and let $I= f(\CB_\beta(f))$. Since $f$ is locally constant on the closed set $\CB_\beta(f)$,
  -- we can choose for each $y\in I$ an open set $U_y$ of $\dom(f)$ such that $U_y\cap \CB_\beta(f)=f^{-1}(\{y\})\cap \CB_\beta(f)$.
  -- Applying the generalized reduction property of open sets \cite[22.16]{kechris} to the open cover of $\dom(f)$ given by $V_y=U_y\cup (\dom(f)\setminus \CB_\beta(f))$ for $y\in I$
  -- yields a clopen partition $(C_y)_{y\in I}$ of $\dom(f)$ with $C_y\subseteq V_y$ for all $y\in I$.
  -- Note that for all $y\in I$ we have $C_y\cap \CB_\beta(f)= f^{-1}(\{y\})\cap \CB_\beta(f)$,
  -- which readily implies that each $f\restr{C_y}$ is simple of $\CB$-rank equal to $\beta+1$ using \cref{CBbasics0}~\cref{CBbasicsfromJSL2}, as desired.
  intros x
  obtain ⟨β, hβ⟩ : ∃ β : Ordinal.{0}, x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
    have h_empty : CBLevel f (CBRank f) = ∅ := by
      -- Apply the lemma that states the CBLevel at the CB rank is empty.
      apply cbLevel_at_cbRank_empty; assumption;
    have h_exists_beta : ∃ β : Ordinal.{0}, x ∉ CBLevel f β := by
      exact ⟨ _, fun hx => h_empty.subset hx ⟩;
    exact exit_ordinal_is_successor x _ h_exists_beta.choose_spec |> fun ⟨ β, hβ₁, hβ₂, hβ₃ ⟩ => ⟨ β, hβ₂, hβ₃ ⟩;
  obtain ⟨U, hU_open, hxU, hU_empty, hU_const⟩ : ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ ∧ ∀ y ∈ U ∩ CBLevel f β, f y = f x := by
    apply isolatedLocus_gives_simple_neighborhood;
    exact Classical.not_not.1 fun h => hβ.2 <| by rw [ CBLevel_succ' ] ; exact ⟨ hβ.1, h ⟩ ;
  obtain ⟨V, hV_clopen, hxV, hV_subset⟩ : ∃ V : Set Baire, IsClopen V ∧ x.val ∈ V ∧ Subtype.val ⁻¹' V ⊆ U := by
    obtain ⟨W, hW_open, hxW, hW_subset⟩ : ∃ W : Set Baire, IsOpen W ∧ x.val ∈ W ∧ Subtype.val ⁻¹' W ⊆ U := by
      rcases hU_open with ⟨ W, hW_open, rfl ⟩ ; use W; aesop;
    exact Exists.elim ( baire_exists_clopen_subset_of_open x.val W hW_open hxW ) fun V hV => ⟨ V, hV.1, hV.2.1, Set.Subset.trans ( Set.preimage_mono hV.2.2 ) hW_subset ⟩;
  refine' ⟨ V, hV_clopen, hxV, _ ⟩;
  apply restriction_to_clopen_is_simple f hf β V hV_clopen ⟨x, hxV, hβ.left⟩ (by
  exact Set.eq_empty_of_forall_notMem fun y hy => hU_empty.subset ⟨ hy.1, hV_subset hy.2 ⟩) (by
  exact ⟨ f x, fun z hz => hU_const z ⟨ hV_subset hz.1, hz.2 ⟩ ⟩)

end DecompositionLemma
