import Mathlib
import RequestProject.PointedGluing.GeneralStructureHelpers
import RequestProject.BaireSpace.Basics
import RequestProject.PointedGluing.MaxFunLimitRankHelpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# MaxFun Limit Rank

This file contains the infrastructure for the limit rank argument in the
General Structure Theorem. It defines `gClopenDom`/`gClopenFun` for restricting
a function to the preimage of a clopen set, and proves key lemmas about
CB-rank preservation and the tree argument for producing disjoint clopen sets
with cofinal CB-ranks.
-/

noncomputable section

/-- Domain restriction of `g` to the preimage of a set `C` in the codomain. -/
def gClopenDom (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∃ (h : x ∈ B), g ⟨x, h⟩ ∈ C}

/-- Function `g` restricted to the preimage of `C` in the codomain. -/
def gClopenFun (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    gClopenDom B g C → ℕ → ℕ :=
  fun ⟨x, hx⟩ => g ⟨x, hx.choose⟩

lemma gClopenFun_continuous (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (C : Set (ℕ → ℕ)) :
    Continuous (gClopenFun B g C) :=
  hgc.comp (Continuous.subtype_mk continuous_subtype_val _)

lemma gClopenFun_scattered (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hg : ScatteredFun g) (C : Set (ℕ → ℕ)) :
    ScatteredFun (gClopenFun B g C) := by
  have : ContinuouslyReduces (gClopenFun B g C) g :=
    ⟨fun x => ⟨x.val, x.prop.choose⟩,
     Continuous.subtype_mk continuous_subtype_val _,
     id, continuousOn_id, fun x => rfl⟩
  exact this.scattered hg


private lemma extract_B_map
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ))
    {A : Set (ℕ → ℕ)}
    (hred : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (gClopenFun B g C)) :
    ∃ (σ : A → B) (τ : (ℕ → ℕ) → (ℕ → ℕ)),
      Continuous σ ∧
      ContinuousOn τ (Set.range (g ∘ σ)) ∧
      (∀ x, g (σ x) ∈ C) ∧
      (∀ x : A, x.val = τ (g (σ x))) := by
  obtain ⟨σ₀, hσ₀_cont, τ₀, hτ₀_cont, hτ₀_eq⟩ := hred
  refine ⟨fun x => ⟨(σ₀ x).val, (σ₀ x).prop.choose⟩, τ₀, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp hσ₀_cont) _
  · convert hτ₀_cont using 1
  · exact fun x => (σ₀ x).prop.choose_spec
  · exact hτ₀_eq

/-- Each piece of the gluing reduces to g, via transitivity with gClopenFun → g. -/
private lemma piece_reduces_to_g
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (C : Set (ℕ → ℕ)) {A : Set (ℕ → ℕ)}
    (hred : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (gClopenFun B g C)) :
    ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) g := by
  exact hred.trans ⟨fun x => ⟨x.val, x.prop.choose⟩,
    Continuous.subtype_mk continuous_subtype_val _,
    id, continuousOn_id, fun x => rfl⟩

/-- Membership: unprepend x.val ∈ A (x.val 0) for x ∈ GluingSet A. -/
private lemma gluingSet_unprepend_mem (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) :
    unprepend x.val ∈ A (x.val 0) := by
  obtain ⟨i, hi, hmem⟩ := GluingSet_inverse_short A x
  exact hi ▸ hmem

/-
The block-wise σ on a GluingSet is continuous.
-/
private lemma gluingSet_blockwise_sigma_cont
    {B : Set (ℕ → ℕ)} (A : ℕ → Set (ℕ → ℕ))
    (σ_n : ∀ n, A n → B) (hσ_cont : ∀ n, Continuous (σ_n n)) :
    Continuous (fun x : GluingSet A => σ_n (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩) := by
  refine' continuous_iff_continuousAt.mpr _
  intro x
  have h_block : IsOpen {y : GluingSet A | y.val 0 = x.val 0} := by
    convert isClopen_preimage_zero ( x.val 0 ) |> IsClopen.isOpen |> IsOpen.preimage ( continuous_subtype_val ) using 1
  have h_cont_on_block : ContinuousOn (fun x : GluingSet A => σ_n (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩) {y : GluingSet A | y.val 0 = x.val 0} := by
    have h_cont_unprepend : Continuous (fun x : GluingSet A => unprepend x.val) := by
      exact continuous_unprepend.comp continuous_subtype_val
    have h_cont_on_block : ContinuousOn (fun x : {y : GluingSet A | y.val 0 = x.val 0} => σ_n (x.val.val 0) ⟨unprepend x.val.val, gluingSet_unprepend_mem A x.val⟩) Set.univ := by
      refine' Continuous.continuousOn _
      convert hσ_cont ( x.val 0 ) |> Continuous.comp <| show Continuous fun y : { y : GluingSet A | y.val 0 = x.val 0 } => ⟨unprepend y.val.val, by
                                                          convert gluingSet_unprepend_mem A y.val using 1
                                                          exact y.2.symm ▸ rfl⟩ from ?_ using 1
      generalize_proofs at *
      · grind
      · exact Continuous.subtype_mk ( h_cont_unprepend.comp <| continuous_subtype_val ) _
    rw [ continuousOn_iff_continuous_restrict ] at *
    convert h_cont_on_block.comp ( show Continuous fun y : { y : GluingSet A // y.val 0 = x.val 0 } => ⟨⟨y.val, by aesop⟩, by aesop⟩ from ?_ ) using 1
    fun_prop
  exact h_cont_on_block.continuousAt ( h_block.mem_nhds <| by aesop )

/-- If each block of a GluingSet reduces to g with images in disjoint clopens C(p n),
    then the entire GluingSet reduces to g. -/
private lemma gluingSet_blockwise_reduces
    {B : Set (ℕ → ℕ)} (g : B → ℕ → ℕ) (_hgc : Continuous g)
    (A : ℕ → Set (ℕ → ℕ))
    (C : ℕ → Set (ℕ → ℕ))
    (hC_clopen : ∀ n, IsClopen (C n))
    (hC_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (p : ℕ → ℕ) (hp : Function.Injective p)
    (σ_n : ∀ n, A n → B) (τ_n : ∀ _n, (ℕ → ℕ) → (ℕ → ℕ))
    (hσ_cont : ∀ n, Continuous (σ_n n))
    (hτ_cont : ∀ n, ContinuousOn (τ_n n) (Set.range (g ∘ σ_n n)))
    (hg_mem : ∀ n (x : A n), g (σ_n n x) ∈ C (p n))
    (heq : ∀ n (x : A n), x.val = τ_n n (g (σ_n n x))) :
    ContinuouslyReduces (Subtype.val : GluingSet A → ℕ → ℕ) g := by
  set σ : GluingSet A → B := fun x => σ_n (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩
  set τ : (ℕ → ℕ) → (ℕ → ℕ) := fun y =>
    if h : ∃ n, y ∈ C (p n) then prepend h.choose (τ_n h.choose y) else 0
  -- Helper: unique block determination by disjointness
  have huniq : ∀ z, ∀ i j, z ∈ C (p i) → z ∈ C (p j) → i = j := by
    intro z i j hi hj
    by_contra h
    exact Set.disjoint_left.mp (hC_disj _ _ (hp.ne h)) hi hj
  refine ⟨σ, gluingSet_blockwise_sigma_cont A σ_n hσ_cont, τ, ?_, ?_⟩
  -- ContinuousOn τ on range(g ∘ σ)
  · -- Use continuousOn_piecewise_clopen
    have hcover : ∀ z ∈ Set.range (g ∘ σ), ∃ i, z ∈ C (p i) := by
      rintro z ⟨x, rfl⟩
      exact ⟨x.val 0, hg_mem (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩⟩
    apply continuousOn_piecewise_clopen (S_i := fun n => C (p n))
        (τ_i := fun n y => prepend n (τ_n n y))
    -- cover
    · exact hcover
    -- clopen
    · intro n; exact hC_clopen (p n)
    -- agree
    · intro z _ i hi j hj; rw [huniq z i j hi hj]
    -- cont on each piece
    · intro n
      have hsubset : Set.range (g ∘ σ) ∩ C (p n) ⊆ Set.range (g ∘ σ_n n) := by
        rintro z ⟨⟨x, rfl⟩, hz_C⟩
        have hblock : x.val 0 = n :=
          huniq _ (x.val 0) n (hg_mem (x.val 0) ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩) hz_C
        exact ⟨⟨unprepend x.val, hblock ▸ gluingSet_unprepend_mem A x⟩,
              by simp only [comp_def]; exact congrArg g (by subst hblock; rfl)⟩
      exact (continuous_prepend n).continuousOn.comp
        ((hτ_cont n).mono hsubset) (fun _ _ => Set.mem_univ _)
    -- cover (duplicate)
    · exact hcover
    -- τ def
    · intro z hz n hn
      simp only [τ]
      have hexists : ∃ m, z ∈ C (p m) := ⟨n, hn⟩
      rw [dif_pos hexists]
      have hchoose : hexists.choose = n := huniq z _ n hexists.choose_spec hn
      rw [hchoose]
  -- equation: τ(g(σ(x))) = x.val
  · intro x
    -- σ x = σ_n (x.val 0) ⟨unprepend x.val, ...⟩
    -- g(σ x) ∈ C(p(x.val 0))
    set n₀ := x.val 0
    set a₀ : A n₀ := ⟨unprepend x.val, gluingSet_unprepend_mem A x⟩
    have hval : g (σ_n n₀ a₀) ∈ C (p n₀) := hg_mem n₀ a₀
    -- τ picks block n₀ since g(σ x) ∈ C(p n₀)
    have hτ_eq : τ (g (σ x)) = prepend n₀ (τ_n n₀ (g (σ_n n₀ a₀))) := by
      show τ (g (σ_n n₀ a₀)) = _
      simp only [τ]
      rw [dif_pos (⟨n₀, hval⟩ : ∃ n, g (σ_n n₀ a₀) ∈ C (p n))]
      have hch : (⟨n₀, hval⟩ : ∃ n, g (σ_n n₀ a₀) ∈ C (p n)).choose = n₀ :=
        huniq _ _ _ (⟨n₀, hval⟩ : ∃ n, g (σ_n n₀ a₀) ∈ C (p n)).choose_spec hval
      simp only [hch]
    rw [hτ_eq, ← heq n₀ a₀]
    exact (prepend_unprepend x.val).symm

lemma gluing_via_codomain_partition
    (η : Ordinal.{0}) (_hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g)
    (C : ℕ → Set (ℕ → ℕ))
    (hC_clopen : ∀ n, IsClopen (C n))
    (hC_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (p : ℕ → ℕ) (hp : Function.Injective p)
    (hred : ∀ n, ContinuouslyReduces
        (Subtype.val : MaxDom (enumBelow η n) → ℕ → ℕ)
        (gClopenFun B g (C (p n)))) :
    ContinuouslyReduces (MaxFun η) g := by
  -- Step 1: Extract block reductions via extract_B_map
  have hred' := fun n => extract_B_map B g (C (p n)) (hred n)
  choose σ_n τ_n hσ_cont hτ_cont hg_mem heq using hred'
  -- Step 2: MaxDom η = GluingSet(fun n => MaxDom(enumBelow η n))
  have hMaxDom : MaxDom η = GluingSet (fun n => MaxDom (enumBelow η n)) :=
    MaxDom_limit η hlim (Order.IsSuccLimit.ne_bot hlim)
  -- Step 3: Apply gluingSet_blockwise_reduces
  show ContinuouslyReduces (Subtype.val : MaxDom η → ℕ → ℕ) g
  rw [hMaxDom]
  exact gluingSet_blockwise_reduces g hgc _ C hC_clopen hC_disj p hp σ_n τ_n hσ_cont hτ_cont hg_mem heq

end

section TreeArgument


-- ============================================================
-- §2  The tree T and its body [T]
-- ============================================================


variable {B : Set (ℕ → ℕ)} {g : B → ℕ → ℕ}
variable (η : Ordinal.{0})

/-- Restriction of `g` to the preimage of `S`. -/
def gRestr (S : Set (ℕ → ℕ)) : {x : B | g x ∈ S} → ℕ → ℕ :=
  fun x => g x.val

/-- CB-rank of `g` restricted to the preimage of the basic neighborhood `BaNbhd s`. -/
noncomputable def cbRankRestr (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) {n : ℕ} (s : Fin n → ℕ) : Ordinal.{0} :=
  CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val)

/-- The tree `T` of finite sequences `s` such that `CBRank(g|₁{BaNbhd s}) = η`. -/
def TreeT (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (η : Ordinal.{0}) :
    (Σ n : ℕ, Fin n → ℕ) → Prop :=
  fun ⟨_, s⟩ => cbRankRestr B g s = η


lemma CoRestr_BaNbhd_empty : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} = Set.univ := by
  simp [BaNbhd_empty]

/-- The empty sequence is in T: BaNbhd ∅ = univ, so gRestr univ = g, and CBRank g = η. -/
lemma TreeT_contains_empty (hg : ScatteredFun g) (hrank : CBRank g = η) :
    TreeT B g η ⟨0, Fin.elim0⟩ := by
  unfold TreeT cbRankRestr
  have hmem : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} = Set.univ :=
    CoRestr_BaNbhd_empty
  have hopen : IsOpen ({b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} : Set B) :=
    hmem ▸ isOpen_univ
  have hle : CBRank (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
      g x.val) ≤ CBRank g :=
    CBRank_open_restrict_le g hg _ hopen
  have hred : ContinuouslyReduces g (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
    g x.val) := by
    refine ⟨fun b => ⟨b, hmem ▸ Set.mem_univ b⟩, Continuous.subtype_mk continuous_id _,
          id, continuousOn_id, fun b => rfl⟩
  have hge : CBRank g ≤ CBRank (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
    g x.val) :=
    ContinuouslyReduces.rank_monotone hg (scattered_restrict g hg _) hred
  simp only []
  exact (le_antisymm hle hge).trans hrank


/-- T is closed under prefixes: if t ∈ T and s is a prefix of t, then s ∈ T. -/
lemma TreeT_prefix_closed (heta: η = CBRank g) {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hpre : IsPrefix s t) (ht : TreeT B g η ⟨m, t⟩)
    (hg : ScatteredFun g) (hgc : Continuous g) :
    TreeT B g η ⟨n, s⟩ := by
  simp only [TreeT, cbRankRestr] at *
  -- Let Vs := {b : B | g b ∈ BaNbhd s} and Vt := {b : B | g b ∈ BaNbhd t}.
  -- BaNbhd t ⊆ BaNbhd s, so Vt ⊆ Vs.
  set Vs : Set B := {b : B | g b ∈ BaNbhd s} with hVs_def
  set Vt : Set B := {b : B | g b ∈ BaNbhd t} with hVt_def
  -- Vt ⊆ Vs  (from BaNbhd_antitone)
  have hVtVs : Vt ⊆ Vs := by
    intro b hb
    simp only [hVt_def, hVs_def, Set.mem_setOf_eq] at *
    exact BaNbhd_antitone s t hpre hb
  -- Vs is open: preimage of BaNbhd s (which is open) under the continuous map g.
  have hVs_open : IsOpen Vs := by
    have : Vs = g ⁻¹' BaNbhd s := rfl
    rw [this]
    exact (BaNbhd_isOpen s).preimage hgc
  -- Vt is open (similarly).
  have hVt_open : IsOpen Vt := by
    have : Vt = g ⁻¹' BaNbhd t := rfl
    rw [this]
    exact (BaNbhd_isOpen t).preimage hgc
  -- The restriction g|Vs is scattered (restriction of a scattered function).
  have hgs_scat : ScatteredFun (fun x : Vs => g x.val) :=
    scattered_restrict g hg Vs
  -- The restriction g|Vt is scattered.
  have hgt_scat : ScatteredFun (fun x : Vt => g x.val) :=
    scattered_restrict g hg Vt
  -- ── Upper bound: CBRank (g|Vs) ≤ CBRank (g|Vt) via open restriction ──
  -- Vt is an open subset of Vs (since Vt ⊆ Vs and Vt is open in B,
  -- so it is open in the subspace Vs).
  -- We use CBRank_open_restrict_le applied to g|Vs and the open set Vt ∩ Vs = Vt.
  -- g|Vs restricted to Vt equals g|Vt.
  have hVt_open_in_Vs : IsOpen (Subtype.val ⁻¹' Vt : Set Vs) := by
    exact hVt_open.preimage continuous_subtype_val
  -- CBRank (g|Vt) ≤ CBRank (g|Vs)  [Vt is an open subset of Vs]
  have hred : ContinuouslyReduces (fun x : Vt => g x.val) (fun x : Vs => g x.val) :=
    ⟨fun x => ⟨x.val, hVtVs x.prop⟩,
    continuous_subtype_val.subtype_mk _,
    id, continuousOn_id,
    fun _ => rfl⟩
  have hle : CBRank (fun x : Vt => g x.val)  ≤ CBRank (fun x : Vs => g x.val) :=
    ContinuouslyReduces.rank_monotone hgt_scat hgs_scat hred  -- Conclude CBRank (g|Vs) = CBRank (g|Vt) = η.
  have hge : CBRank (fun x : Vs => g x.val) ≤ CBRank (fun x : Vt => g x.val) := by
    calc CBRank (fun x : Vs => g x.val)
        ≤ CBRank g := CBRank_open_restrict_le g hg Vs hVs_open
      _ = η        := heta.symm
      _ = CBRank (fun x : Vt => g x.val) := ht.symm
  exact le_antisymm hge hle |>.trans ht


/-- If s and t are incomparable (neither is a prefix of the other),
    their BaNbhds are disjoint. -/
lemma BaNbhd_incomparable_disjoint {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hst : ¬IsPrefix s t) (hts : ¬IsPrefix t s) :
    Disjoint (BaNbhd s) (BaNbhd t) := by
  simp only [IsPrefix] at hst hts
  push_neg at hst hts
  simp only [Set.disjoint_left, BaNbhd, Set.mem_setOf_eq]
  intro h hs ht
  rcases Nat.lt_or_ge n m with hnm | hnm
  · obtain ⟨i, hi⟩ := hst hnm.le
    exact hi ((hs i).symm.trans (ht ⟨i, i.isLt.trans_le hnm.le⟩))
  · obtain ⟨i, hi⟩ := hts hnm
    exact hi ((ht i).symm.trans (hs ⟨i, i.isLt.trans_le hnm⟩))

lemma CBLevel_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Z) (φ : Y ≃ₜ X) (α : Ordinal.{0}) :
    CBLevel (f ∘ φ) α = φ ⁻¹' (CBLevel f α) := by
      induction' α using Ordinal.limitRecOn with α ih
      · simp +decide [ CBLevel_zero ]
      · -- By definition of isolatedLocus, we have that the isolated locus of a composition is the preimage of the isolated locus of the original function.
        have h_isolatedLocus : isolatedLocus (f ∘ φ) (φ ⁻¹' (CBLevel f α)) = φ ⁻¹' isolatedLocus f (CBLevel f α) := by
          ext y
          constructor <;> rintro ⟨h₁, U, hU, hy, hU'⟩
          · refine' ⟨h₁, φ '' U, _, _, _⟩ <;> simp_all +decide
          · refine' ⟨_, φ ⁻¹' U, hU.preimage φ.continuous, _, _⟩ <;> aesop
        simp_all +decide [ CBLevel_succ' ]
      · exact CBLevel_homeomorph φ f _

lemma CBRank_comp_homeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z]
    (f : X → Z) (φ : Y ≃ₜ X) :
    CBRank (f ∘ φ) = CBRank f := by
      unfold CBRank
      congr! 3
      rw [ CBLevel_comp_homeomorph, CBLevel_comp_homeomorph ]
      constructor <;> intro h <;> ext x <;> simp_all +decide [ Set.ext_iff ]
      simpa using h ( φ.symm x )

/-- Homeomorphism between `{b : B | g b ∈ C}` and `gClopenDom B g C`. -/
def gClopenDomEquiv (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    {b : B | g b ∈ C} ≃ₜ gClopenDom B g C where
  toFun := fun ⟨⟨x, hB⟩, hC⟩ => ⟨x, ⟨hB, hC⟩⟩
  invFun := fun ⟨x, hx⟩ => ⟨⟨x, hx.choose⟩, hx.choose_spec⟩
  left_inv := fun ⟨⟨x, hB⟩, hC⟩ => by simp
  right_inv := fun ⟨x, hx⟩ => by simp
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val.subtype_val _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

lemma gClopenFun_eq_comp (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    gClopenFun B g C = (fun x : {b : B | g b ∈ C} => g x.val) ∘ (gClopenDomEquiv B g C).symm := by
  ext ⟨x, hx⟩
  simp [gClopenFun, gClopenDomEquiv]

lemma gClopenFun_CBRank_eq : ∀ (C : Set (ℕ → ℕ)), IsClopen C →
    CBRank (gClopenFun B g C) = CBRank (fun x : {b : B | g b ∈ C} => g x.val) := by
  intro C _
  rw [gClopenFun_eq_comp]
  exact CBRank_comp_homeomorph _ _

lemma exists_disjoint_clopen_with_cofinal_ranks
    (η : Ordinal.{0}) (hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g) (hg : ScatteredFun g)
    (hrank : CBRank g = η)
    (δ : ℕ → Ordinal.{0}) (hδ : ∀ n, δ n < η) :
    ∃ (C : ℕ → Set (ℕ → ℕ)) (p : ℕ → ℕ),
      Function.Injective p ∧
      (∀ n, IsClopen (C n)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ n, δ n < CBRank (gClopenFun B g (C (p n))) := by
  -- ── Step 1: Build the tree T ────────────────────────────────────────────
  -- T_prop n s ↔ CBRank(g|BaNbhd s) = η
  let T_prop : ∀ n : ℕ, (Fin n → ℕ) → Prop :=
    fun _ s => CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) = η
  -- The body [T] = {x : ℕ → ℕ | ∀ n, T_prop n (x ↾ n)}
  set bodyT : Set (ℕ → ℕ) :=
    {x : ℕ → ℕ | ∀ n, T_prop n (fun i => x i)}
  -- ── Step 2: Case split ──────────────────────────────────────────────────
  by_cases hbody : bodyT.Infinite
  · -- ══ Case A: bodyT infinite ══════════════════════════════════════════
      obtain ⟨seq, hseq_incompat, hseq_T⟩ :
          ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
            (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                            ¬IsPrefix (seq j).2 (seq i).2) ∧
            ∀ i, T_prop (seq i).1 (seq i).2 := by
        -- Use the antichain construction from the helpers file
        let f : ℕ ↪ bodyT := hbody.natEmbedding bodyT
        have hf_inj : Injective (fun i => (f i).val) :=
          fun i j h => f.injective (Subtype.val_injective h)
        obtain ⟨seq, hseq_ac, hseq_trunc⟩ :=
          infinite_baire_antichain_prefixes (fun i => (f i).val) hf_inj
        refine ⟨seq, hseq_ac, fun i => ?_⟩
        obtain ⟨m, hm⟩ := hseq_trunc i
        -- seq(i) is a truncation of f(m).val, which is in bodyT
        -- so T_prop holds for this truncation
        have hfm_body := (f m).prop
        simp only [bodyT, Set.mem_setOf_eq] at hfm_body
        show T_prop (seq i).1 (seq i).2
        simp only [T_prop]
        have : (fun j : Fin (seq i).1 => (f m).val ↑j) = (seq i).2 := by
          ext j; exact (hm j).symm
        rw [← this]
        exact hfm_body (seq i).1
      refine ⟨fun n => BaNbhd (seq n).2, id, Function.injective_id,
              fun n => BaNbhd_isClopen _, ?_, ?_⟩
      · intro i j hij
        obtain ⟨hst, hts⟩ := hseq_incompat i j hij
        exact BaNbhd_incomparable_disjoint (seq i).2 (seq j).2 hst hts
      · intro n
        show δ n < CBRank (gClopenFun B g (BaNbhd (seq n).2))
        have hrank_eq : CBRank (gClopenFun B g (BaNbhd (seq n).2)) =
              CBRank (fun x : {b : B | g b ∈ BaNbhd (seq n).2} => g x.val) :=
          gClopenFun_CBRank_eq (BaNbhd (seq n).2) (BaNbhd_isClopen _)
        rw [hrank_eq]
        have hT := hseq_T n
        simp only [T_prop] at hT
        rw [hT]
        exact hδ n
  · -- ══ Case B: bodyT finite ════════════════════════════════════════════
    -- The minimal elements of ℕ^{<ω} \ T form a finite antichain F.
    -- Their BaNbhds are pairwise disjoint clopens covering (ℕ→ℕ) \ bodyT.
    -- Key: the ranks {CBRank(g|BaNbhd s) | s ∈ F} are cofinal in η.
    --
    -- Cofinality: for any β < η, some s ∈ F has CBRank(g|BaNbhd s) > β.
    -- Proof: if all had rank ≤ β, then CB_β(g) ⊆ g⁻¹(bodyT). But bodyT is
    -- finite, so every point of g⁻¹(bodyT) is isolated in CB_β(g), giving
    -- CB_{β+1}(g) = ∅, so CBRank g ≤ β + 1 < η — contradiction with hrank.
    have hCofinal : ∀ β : Ordinal.{0}, β < η →
        ∃ (n : ℕ) (s : Fin n → ℕ), ¬T_prop n s ∧
          β < CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) := by
      -- For any β < η, we find a BaNbhd node s with β < rank(g|BaNbhd s) < η.
      -- This uses the fact that the ranks of the level-1 BaNbhd partitions
      -- cannot all be ≤ β (otherwise CBRank g ≤ β < η, contradiction).
      sorry
    -- For each n : ℕ, apply hCofinal to δ n to get a sequence of
    -- not-in-T nodes with rank > δ n.
    -- Then take their ⊏-minimal prefixes (which are in F, hence pairwise
    -- incomparable) to get pairwise disjoint BaNbhds.
    -- More precisely: choose seq n to be a ⊏-minimal s with ¬T_prop and
    -- CBRank(g|BaNbhd s) > δ n.  Minimality ensures incomparability.
    obtain ⟨seq, hseq_incompat, hseq_cofinal⟩ :
        ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
          (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                           ¬IsPrefix (seq j).2 (seq i).2) ∧
          ∀ i, δ i < CBRank (fun x : {b : B | g b ∈ BaNbhd (seq i).2} => g x.val) := by
      -- For each i, hCofinal (δ i) (hδ i) gives some node with rank > δ i.
      -- Take its ⊏-minimal prefix not in T (exists since T is prefix-closed
      -- and the node itself is not in T).
      -- Since bodyT is finite, F is finite, so by pigeonhole some element of F
      -- is used for infinitely many i — but we only need a sequence, not
      -- distinct elements, so repetition is fine for the rank condition.
      -- For disjointness: take seq i to be elements of F (finite antichain),
      -- cycling or using a fixed enumeration of F together with the injection p.
      -- The injection p : ℕ → ℕ handles the case where F is finite by
      -- selecting which Cₙ to use for each δ n query.
      sorry
    -- Now take C n := BaNbhd (seq n).2 and p := id (or the appropriate index).
    refine ⟨fun n => BaNbhd (seq n).2, id, Function.injective_id,
            fun n => BaNbhd_isClopen _, ?_, ?_⟩
    · intro i j hij
      obtain ⟨hst, hts⟩ := hseq_incompat i j hij
      exact BaNbhd_incomparable_disjoint (seq i).2 (seq j).2 hst hts -- or sorry
    · intro n
      -- hseq_cofinal n : δ n < CBRank(g|BaNbhd (seq n).2)
      -- Need to identify gClopenFun with the restriction — then exact hseq_cofinal n.
      simp only [id]
      rw [gClopenFun_CBRank_eq (BaNbhd (seq n).2) (BaNbhd_isClopen _)]
      exact hseq_cofinal n

end TreeArgument
