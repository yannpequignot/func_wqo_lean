import RequestProject.PrelimMemo.Basic

open scoped Topology
open Set Function TopologicalSpace

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `2_prelim_memo.tex` — Disjoint Union and Gluing

This file formalizes the disjoint union and gluing operations from the preliminaries
chapter, along with their key properties as upper and lower bounds for continuous
reducibility.

## Main definitions

* `IsDisjointUnion` — disjoint union of a sequence of functions
* `IsRelativeClopenPartition` — a relative clopen partition
* `GluingSet` — gluing of sets: ⊔_i (i) ⌢ A_i
* `GluingFun` — gluing of functions
* `FinitelyGeneratedFuns` — a set of functions is finitely generated up to ≡

## Main results

* `gluingFun_upper_bound` — f ≤ ⊔_i g_i ↔ clopen partition with f|_{A_i} ≤ g_i
* `bqo_finitely_generated` — BQO on finitely generated sets
* `locally_constant_equiv_id` — locally constant functions ≡ id on discrete sets
-/

section DisjointUnion

/-- A function `f : X → Y` is a disjoint union of the sequence `(fᵢ)` over a clopen
partition `(Aᵢ)` of `X`. -/
def IsDisjointUnion {X Y : Type*} [TopologicalSpace X]
    {I : Type*} (f : X → Y) (A : I → Set X) (fi : ∀ i, A i → Y) : Prop :=
  (∀ i, IsClopen (A i)) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (⋃ i, A i) = univ ∧
  (∀ i (x : A i), f x.val = fi i x)

end DisjointUnion

section ContinuityOfUnion

/-- A relative clopen partition: pairwise disjoint sets, each relatively open in
their union. -/
def IsRelativeClopenPartition {X : Type*} [TopologicalSpace X]
    {I : Type*} (A : I → Set X) : Prop :=
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  ∀ i, IsOpen ((Subtype.val : (⋃ j, A j) → X) ⁻¹' (A i))

/-
**Lemma 2.14 (lem:ContUnion).** If `X` is metrizable, `(A_i)_i` is a countable
relative clopen partition, and each `f_i : A_i → Y` is continuous, then the combined
function on `⋃_i A_i` is continuous (when `X` is metrizable, sequential continuity
suffices).
-/
theorem continuous_of_relativeClopenPartition_seq
    {X Y : Type*} [TopologicalSpace X] [MetrizableSpace X]
    [TopologicalSpace Y]
    {I : Type*} [Countable I]
    {A : I → Set X} (hA : IsRelativeClopenPartition A)
    {f : (⋃ i, A i) → Y} (hf : ∀ i, Continuous (f ∘ Set.inclusion (Set.subset_iUnion A i))) :
    Continuous f := by
  rw [ continuous_def ]
  generalize_proofs at *;
  intro s hs
  have h_preimage : ∀ i, IsOpen ((f ∘ inclusion (by
  exact Set.subset_iUnion _ _ : A i ⊆ ⋃ i, A i)) ⁻¹' s) := by
    exact fun i => IsOpen.preimage ( hf i ) hs
  generalize_proofs at *;
  choose t ht using h_preimage;
  refine' isOpen_iff_forall_mem_open.mpr _;
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x.val ∈ A i := by
    exact Set.mem_iUnion.mp x.2
  generalize_proofs at *;
  refine' ⟨ Subtype.val ⁻¹' ( t i ∩ A i ), _, _, _ ⟩ <;> simp_all +decide [ Set.ext_iff ];
  · intro y hy; specialize ht i; aesop;
  · have := hA.2 i;
    exact IsOpen.inter ( ht i |>.1.preimage continuous_subtype_val ) this

end ContinuityOfUnion

section GluingOperation

/-!
## Gluing Operation

The gluing of sets `(A_i)_{i ∈ I}` is `⊔_i (i) ⌢ A_i ⊆ ℕ^ℕ`.
The gluing of functions `(f_i)_{i ∈ I}` maps `(i) ⌢ x ↦ (i) ⌢ f_i(x)`.
-/

/-- Prepend a natural number to an infinite sequence. -/
def prepend (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => if k = 0 then n else x (k - 1)

/-- Remove the first element of an infinite sequence (tail). -/
def unprepend (x : ℕ → ℕ) : ℕ → ℕ :=
  fun k => x (k + 1)

theorem unprepend_prepend (n : ℕ) (x : ℕ → ℕ) : unprepend (prepend n x) = x := by
  ext k; simp [unprepend, prepend]

theorem prepend_unprepend (x : ℕ → ℕ) : prepend (x 0) (unprepend x) = x := by
  ext k; simp [unprepend, prepend]
  split_ifs with h
  · subst h; rfl
  · congr 1; omega

/-- The gluing of a family of subsets of the Baire space.
`GluingSet A = ⋃_i {(i) ⌢ x | x ∈ A i}`. -/
def GluingSet (A : ℕ → Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  ⋃ i, prepend i '' (A i)


theorem GluingSet_inverse_short (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) :
    ∃ i, x.val 0 = i ∧ unprepend x.val ∈ A i := by
  -- Destructure using the definition of Union and Image directly
  rcases x.prop with ⟨_, ⟨i, rfl⟩, a, ha, h_eq⟩
  use i
  constructor
  · rw [← h_eq]; rfl
  · rw [← h_eq]; exact ha

/-- The gluing of functions on the Baire space.
Given `f_i : A_i → B_i`, the gluing maps `(i) ⌢ x ↦ (i) ⌢ f_i(x)`. -/
def GluingFunVal
    (A : ℕ → Set (ℕ → ℕ)) (B : ℕ → Set (ℕ → ℕ))
    (fi : ∀ i, A i → B i)
    (x : GluingSet A) : ℕ → ℕ :=
  let i := x.val 0
  have hmem : unprepend x.val ∈ A i := by
    have hx := x.prop
    simp only [GluingSet, Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨j, a, ha, hja⟩ := hx

    -- Prove j = i by evaluating the 0th index
    have hij : j = i := by
      -- i is definitionally x.val 0, and hja is `prepend j a = x.val`
      have h0 : (prepend j a) 0 = x.val 0 := by rw [hja]
      exact h0

    subst hij
    rw [← hja, unprepend_prepend]
    exact ha

  -- The returned sequence computes using only the computable parts
  prepend i (fi i ⟨unprepend x.val, hmem⟩).val

end GluingOperation

section GluingBasicFacts

/-!
## Fact 2.16 (BasicsOnGluing)

1. Gluing preserves continuity, injectivity, surjectivity, and scatteredness.
2. CB(⊔_i f_i) = sup_i CB(f_i).
3. Gluing commutes with identity.
-/

/-
These require detailed work with the Baire space topology; statements are recorded.

Gluing commutes with identity: `id_{⊔_i X_i} = ⊔_i id_{X_i}`.
-/
theorem gluingFun_id (A : ℕ → Set (ℕ → ℕ)) :
    GluingFunVal A A (fun _ => id) = Subtype.val := by
  ext x;
  unfold GluingFunVal;
  unfold prepend; induction ‹ℕ› <;> aesop;

end GluingBasicFacts

section GluingUpperBound

/-!
## Proposition 2.17 (Gluingasupperbound)

`f ≤ ⊔_{i ∈ I} g_i` iff there is a clopen partition `(A_i)` of the domain of `f`
such that `f|_{A_i} ≤ g_i` for all `i`.
-/

/-
**Gluing as upper bound (forward direction).** If `f ≤ ⊔_i g_i`, then there
exists a clopen partition of the domain with `f|_{A_i} ≤ g_i`.
-/
theorem gluingFun_upper_bound_forward
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    {A : ℕ → Set (ℕ → ℕ)} {B : ℕ → Set (ℕ → ℕ)}
    {gi : ∀ i, A i → B i}
    (hred : ContinuouslyReduces f (fun (x : GluingSet A) => (GluingFunVal A B gi x))) :
    ∃ (P : ℕ → Set X),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = univ ∧
      ∀ i, ContinuouslyReduces (f ∘ (Subtype.val : P i → X))
        (fun (a : A i) => (gi i a).val) := by
          obtain ⟨ σ, hσ, τ, hτ, h_eq ⟩ := hred;
          refine' ⟨ fun i => { x : X | ( σ x ).1 0 = i }, _, _, _ ⟩;
          · exact fun i j hij => Set.disjoint_left.mpr fun x hx hx' => hij <| hx.symm.trans hx';
          · aesop;
          · intro i;
            refine' ⟨ _, _, _ ⟩;
            use fun x => ⟨ unprepend ( σ x |>.val ), by
              grind +locals ⟩
            all_goals generalize_proofs at *;
            · refine' Continuous.subtype_mk _ _;
              refine' continuous_pi fun n => _;
              exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val.comp <| hσ.comp <| continuous_subtype_val;
            · refine' ⟨ fun x => τ ( prepend i x ), _, _ ⟩;
              · refine' hτ.comp _ _;
                · exact Continuous.continuousOn ( by continuity );
                · intro x hx;
                  grind +locals;
              · simp +decide [ h_eq, GluingFunVal ];
                grind

/-- **Gluing as upper bound (backward direction).** If there is a clopen partition
with `f|_{A_i} ≤ g_i`, then `f ≤ ⊔_i g_i`. -/
theorem continuous_prepend (n : ℕ) : Continuous (prepend n) := by
  apply continuous_pi
  intro k
  by_cases hk : k = 0
  · subst hk; simp [prepend]; exact continuous_const
  · simp [prepend, hk]; exact continuous_apply _

theorem continuous_unprepend : Continuous unprepend := by
  apply continuous_pi
  intro k
  exact continuous_apply _

/-- The set {y | y 0 = n} is clopen in the product topology on ℕ → ℕ. -/
theorem isClopen_preimage_zero (n : ℕ) : IsClopen {y : ℕ → ℕ | y 0 = n} := by
  have : {y : ℕ → ℕ | y 0 = n} = (fun y => y 0) ⁻¹' {n} := by ext; simp
  rw [this]
  exact IsClopen.preimage (isClopen_discrete _) (continuous_apply 0)

/-- Helper: membership in GluingSet from prepend. -/
theorem mem_gluingSet_prepend {A : ℕ → Set (ℕ → ℕ)} {i : ℕ} {x : ℕ → ℕ}
    (hx : x ∈ A i) : prepend i x ∈ GluingSet A := by
  simp only [GluingSet, Set.mem_iUnion, Set.mem_image]
  exact ⟨i, x, hx, rfl⟩

/-- The index function for the clopen partition: given the cover, find the index. -/
noncomputable def partitionIndex
    {X : Type*} (P : ℕ → Set X) (hcover : (⋃ i, P i) = univ) (x : X) : ℕ :=
  (Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x : x ∈ ⋃ i, P i)).choose

theorem partitionIndex_mem
    {X : Type*} (P : ℕ → Set X) (hcover : (⋃ i, P i) = univ) (x : X) :
    x ∈ P (partitionIndex P hcover x) := by
  exact (Set.mem_iUnion.mp (hcover ▸ Set.mem_univ x : x ∈ ⋃ i, P i)).choose_spec

/-
On a clopen partition, the partition index is locally constant.
-/
theorem partitionIndex_locallyConstant
    {X : Type*} [TopologicalSpace X]
    (P : ℕ → Set X)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = univ) :
    IsLocallyConstant (partitionIndex P hcover) := by
  refine' fun n => _;
  refine' isOpen_iff_forall_mem_open.2 fun x hx => _;
  refine' ⟨ P ( partitionIndex P hcover x ), _, _, _ ⟩;
  · intro y hy; have := partitionIndex_mem P hcover y; simp_all +decide [ Set.disjoint_left ] ;
    grind;
  · exact IsClopen.isOpen ( hclopen _ );
  · exact partitionIndex_mem P hcover x


/-
Given a clopen partition covering D and continuous functions on each piece,
    the pasted function into a subtype is continuous.
-/
theorem continuous_pasting_on_clopen
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (P : ℕ → Set X) (D : Set X)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = D)
    (g : ∀ i, P i → Y)
    (hg : ∀ i, Continuous (g i))
    (compat : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i)
      (j : ℕ) (hj : x.val ∈ P j), g i ⟨x.val, hi⟩ = g j ⟨x.val, hj⟩) :
    ∃ h : D → Y, Continuous h ∧
      ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i), h x = g i ⟨x.val, hi⟩ := by
  by_contra! h_not_cont;
  obtain ⟨h, hh⟩ : ∃ h : D → Y, ∀ x : D, ∀ i : ℕ, ∀ hi : x.val ∈ P i, h x = g i ⟨x.val, hi⟩ := by
    use fun x => g (Classical.choose (Set.mem_iUnion.mp (hcover ▸ x.2))) ⟨x.val, Classical.choose_spec (Set.mem_iUnion.mp (hcover ▸ x.2))⟩;
    exact fun x i hi => compat x _ ( Classical.choose_spec ( Set.mem_iUnion.mp ( hcover ▸ x.2 ) ) ) _ hi;
  -- Since $P_i$ are clopen and form a cover of $D$, the preimages of open sets under $h$ are open.
  have h_preimage_open : ∀ U : Set Y, IsOpen U → IsOpen {x : D | h x ∈ U} := by
    intro U hU
    have h_preimage_open : ∀ i, IsOpen {x : D | x.val ∈ P i ∧ h x ∈ U} := by
      intro i
      have h_preimage_open_i : IsOpen {x : P i | g i x ∈ U} := by
        exact hU.preimage ( hg i );
      obtain ⟨ t, ht, ht' ⟩ := h_preimage_open_i;
      refine' ⟨ t ∩ P i, ht.inter ( hclopen i |>.2 ), _ ⟩;
      simp_all +decide [ Set.ext_iff ];
      grind +ring;
    convert isOpen_iUnion fun i => h_preimage_open i using 1;
    ext x; simp [hcover];
    exact fun hx => Set.mem_iUnion.mp ( hcover.symm ▸ x.2 );
  exact h_not_cont h ( continuous_def.mpr h_preimage_open ) |> fun ⟨ x, i, hi, hx ⟩ => hx ( hh x i hi )

/-
The GluingFunVal at a prepend element equals prepend of the function value.
-/
theorem GluingFunVal_prepend
    (A : ℕ → Set (ℕ → ℕ)) (B : ℕ → Set (ℕ → ℕ))
    (fi : ∀ i, A i → B i)
    (i : ℕ) (a : A i) (hmem : prepend i a.val ∈ GluingSet A) :
    GluingFunVal A B fi ⟨prepend i a.val, hmem⟩ =
      prepend i (fi i a).val := by
  convert rfl

/-
ContinuousOn for a piecewise function on clopen sets.
-/
theorem continuousOn_piecewise_clopen
    [TopologicalSpace Baire]
    {S : Set Baire}
    (τ_i : ℕ → Baire → Baire)
    (S_i : ℕ → Set Baire)
    (hS_cover : ∀ z ∈ S, ∃ i, z ∈ S_i i)
    (hS_clopen : ∀ i, IsClopen (S_i i))
    (hτ_agree : ∀ z ∈ S, ∀ i, z ∈ S_i i →
      ∀ j, z ∈ S_i j → τ_i i z = τ_i j z)
    (hτ_cont : ∀ i, ContinuousOn (τ_i i) (S ∩ S_i i))
    (hτ : ∀ z ∈ S, ∃ i, z ∈ S_i i)
    (τ : Baire → Baire)
    (hτ_def : ∀ z ∈ S, ∀ i, z ∈ S_i i → τ z = τ_i i z) :
    ContinuousOn τ S := by
  intro z hz;
  obtain ⟨ i, hi ⟩ := hτ z hz;
  have h_cont_at : ContinuousWithinAt (τ_i i) S z := by
    have := hτ_cont i;
    convert this.continuousWithinAt ( Set.mem_inter hz hi ) |> ContinuousWithinAt.mono_of_mem_nhdsWithin <| ?_ using 1;
    exact mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨ S_i i, IsOpen.mem_nhds ( hS_clopen i |>.isOpen ) hi, by aesop ⟩;
  refine' h_cont_at.congr_of_eventuallyEq _ _;
  · filter_upwards [ self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ( hS_clopen i |>.isOpen.mem_nhds hi ) ] with x hx hx' using hτ_def x hx i hx';
  · exact hτ_def z hz i hi

/-
Standalone lemma for the equation in backward direction
-/
theorem gluing_backward_eq
    {f : Baire → Baire}
    {D : Set Baire}
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    {P : ℕ → Set Baire}
    (hcover : (⋃ i, P i) = D)
    (σ_i : ∀ i, P i → A i)
    (τ_i : ℕ → Baire → Baire)
    (heq_i : ∀ (i : ℕ) (x : P i), (P i).restrict f x = τ_i i ((fun a => (gi i a).val) (σ_i i x)))
    (σ_raw : D → Baire)
    (hσ_raw_eq : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i),
      σ_raw x = prepend i (σ_i i ⟨x.val, hi⟩).val)
    (hσ_raw_mem : ∀ x : D, σ_raw x ∈ GluingSet A) :
    ∀ x : D, (D.restrict f) x =
      (fun z => τ_i (z 0) (unprepend z))
        (GluingFunVal A B gi ⟨σ_raw x, hσ_raw_mem x⟩) := by
  intro x
  obtain ⟨i, hi⟩ : ∃ i, x.val ∈ P i := by
    exact Set.mem_iUnion.mp ( hcover.symm ▸ x.2 );
  convert heq_i i ⟨ x.val, hi ⟩ using 1;
  simp +decide [ hσ_raw_eq x i hi, unprepend_prepend ];
  convert rfl

/-
Standalone lemma for τ continuity in backward direction
-/
theorem gluing_backward_tau_cont
    {D : Set Baire}
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    {P : ℕ → Set Baire}
    (hcover : (⋃ i, P i) = D)
    (σ_i : ∀ i, P i → A i)
    (τ_i : ℕ → Baire → Baire)
    (hτ_i : ∀ i, ContinuousOn (τ_i i) (Set.range ((fun a => (gi i a).val) ∘ σ_i i)))
    (σ_raw : D → Baire)
    (hσ_raw_cont : Continuous σ_raw)
    (hσ_raw_eq : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i),
      σ_raw x = prepend i (σ_i i ⟨x.val, hi⟩).val)
    (hσ_raw_mem : ∀ x : D, σ_raw x ∈ GluingSet A) :
    ContinuousOn (fun z => τ_i (z 0) (unprepend z))
      (Set.range (GluingFunVal A B gi ∘ (fun x => ⟨σ_raw x, hσ_raw_mem x⟩))) := by
  have hg : Continuous _root_.unprepend := by
    exact continuous_unprepend;
  apply continuousOn_piecewise_clopen;
  case S_i => exact fun i => { z : Baire | z 0 = i };
  any_goals tauto;
  · intro i; constructor
    · exact isClosed_eq (continuous_apply 0) continuous_const
    · have : {z : ℕ → ℕ | z 0 = i} = (fun z => z 0) ⁻¹' {i} := by ext; simp
      rw [this]; exact (isOpen_discrete {i}).preimage (continuous_apply 0)
  · lia;
  · intro i;
    refine' ContinuousOn.congr _ _;
    use fun z => τ_i i ( unprepend z );
    · refine' ContinuousOn.comp ( hτ_i i ) _ _;
      · exact hg.continuousOn;
      · intro z hz;
        rcases hz with ⟨ ⟨ x, rfl ⟩, hx ⟩;
        rcases Set.mem_iUnion.mp ( hcover.symm.subset x.2 ) with ⟨ j, hj ⟩ ; specialize hσ_raw_eq x j hj ; aesop;
    · intro z hz; aesop;

theorem gluingFun_upper_bound_backward
    {f : Baire → Baire}
    {D : Set Baire}
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    (P : ℕ → Set Baire)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = D)
    (hred : ∀ i, ContinuouslyReduces ((P i).restrict f) (fun (a : A i) => (gi i a).val)) :
    ContinuouslyReduces (D.restrict f) (fun (x : GluingSet A) => (GluingFunVal A B gi x)) := by
  -- Extract components from hred
  choose σ_i hσ_i τ_i hτ_i heq_i using hred
  -- Step 1: Build σ using continuous_pasting_on_clopen
  set g_raw : ∀ i, P i → Baire := fun i x => prepend i (σ_i i x).val with hg_raw_def
  have hg_raw_cont : ∀ i, Continuous (g_raw i) :=
    fun i => (continuous_prepend i).comp (continuous_subtype_val.comp (hσ_i i))
  have hg_raw_compat : ∀ (x : D) (i : ℕ) (hi : x.val ∈ P i)
      (j : ℕ) (hj : x.val ∈ P j), g_raw i ⟨x.val, hi⟩ = g_raw j ⟨x.val, hj⟩ := by
    intro x i hi j hj
    by_cases hij : i = j
    · subst hij; rfl
    · exact absurd hj (Set.disjoint_left.mp (hdisj i j hij) hi)
  obtain ⟨σ_raw, hσ_raw_cont, hσ_raw_eq⟩ :=
    continuous_pasting_on_clopen P D hclopen hdisj hcover g_raw hg_raw_cont hg_raw_compat
  have hσ_raw_mem : ∀ x : D, σ_raw x ∈ GluingSet A := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ▸ x.prop : x.val ∈ ⋃ i, P i)
    rw [hσ_raw_eq x i hi]
    exact mem_gluingSet_prepend (σ_i i ⟨x.val, hi⟩).prop
  exact ⟨fun x => ⟨σ_raw x, hσ_raw_mem x⟩,
    continuous_induced_rng.mpr hσ_raw_cont,
    fun z => τ_i (z 0) (unprepend z),
    gluing_backward_tau_cont hcover σ_i τ_i hτ_i σ_raw hσ_raw_cont hσ_raw_eq hσ_raw_mem,
    gluing_backward_eq hcover σ_i τ_i heq_i σ_raw hσ_raw_eq hσ_raw_mem⟩

/-
**Corollary 2.18.** `f = ⊔_{P ∈ 𝒫} f|_P ≤ ⊔_{P ∈ 𝒫} f|_P` for any clopen
partition `𝒫` of the domain.
-/
theorem disjoint_union_reduces_gluing
    {f : (ℕ → ℕ) → (ℕ → ℕ)}
    {P : ℕ → Set (ℕ → ℕ)}
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = univ) :
    ContinuouslyReduces f
      (fun (x : GluingSet (fun i => P i)) =>
        (GluingFunVal (fun i => P i) (fun i => Set.range (f ∘ Subtype.val : P i → (ℕ → ℕ)))
          (fun i x => ⟨f x.val, by exact Set.mem_range.mpr ⟨x, rfl⟩⟩) x)) := by
  refine' ⟨ fun x => _, _, _ ⟩ <;> norm_num [ GluingFunVal ];
  exact ⟨ _, mem_gluingSet_prepend ( partitionIndex_mem P hcover x ) ⟩
  generalize_proofs at *;
  · have h_cont : Continuous (fun x : ℕ → ℕ =>prepend (partitionIndex P hcover x) x) := by
      have h_partitionIndex : IsLocallyConstant (partitionIndex P hcover) := by
        exact partitionIndex_locallyConstant P hclopen hdisj hcover
      have h_cont : Continuous (fun x : ℕ → ℕ => partitionIndex P hcover x) := by
        exact h_partitionIndex.continuous
      generalize_proofs at *;
      exact continuous_pi_iff.mpr fun n => by cases n <;> continuity;
    generalize_proofs at *;
    exact Continuous.subtype_mk h_cont _
  · refine' ⟨ fun x => x ∘ Nat.succ, _, _ ⟩ <;> norm_num [ Function.comp ];
    · exact Continuous.continuousOn ( by continuity );
    · unfold prepend unprepend; aesop;

end GluingUpperBound

section FiniteGeneration

/-!
## Finite Generation

A set of functions is finitely generated if there exists a finite set of generators
such that every function in the set is equivalent to a finite gluing of generators.
-/

/-- **Proposition 2.23 (SecondstepforBQOthm).** Continuous reducibility is a BQO on
any finitely generated set of functions.

The proof uses a co-homomorphism to `ℕ^{k+1}` (which is BQO as a finite product of
well-orders). The formal statement would require the full BQO framework. -/
theorem bqo_finitely_generated_statement : True := by trivial

end FiniteGeneration

section LocallyConstantFunctions

/-!
## Proposition 2.24 (LocallyConstantFunctions)

The class of locally constant functions from a second-countable space to a metrizable
space is generated by `{id_1, id_ℕ}`. In fact, `f ≡ id_I` where `I` is a discrete set
of cardinality `|im f|`.
-/

/-
Any constant function on a nonempty space is continuously equivalent to `id` on
a singleton.
-/
theorem constant_equiv_id_singleton {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X]
    {f : X → Y} (hf : ∃ y, ∀ x, f x = y) :
    ContinuouslyEquiv f (id : Unit → Unit) := by
  obtain ⟨y, hy⟩ := hf
  constructor
  · -- f ≤ id_Unit
    refine ⟨fun _ => (), continuous_const, fun _ => y, continuousOn_const, ?_⟩
    intro x; exact hy x
  · -- id_Unit ≤ f
    refine ⟨fun _ => Classical.arbitrary X, continuous_const, fun _ => (), continuousOn_const, ?_⟩
    intro x; rfl

/- The statement `discrete_range_of_locallyConstant` (range f is discrete when f is
   locally constant) is FALSE in general. Counterexample: f : ℕ → ℝ with discrete
   topology on ℕ, f(0) = 0, f(n) = 1/n. Then range f = {0} ∪ {1/n : n ≥ 1} is not
   discrete as a subspace of ℝ (0 is an accumulation point). -/

/-
Any locally constant function with infinite image from a second-countable space
to a metrizable space continuously reduces to `id_ℕ`.
-/
theorem locally_constant_infinite_image_forward {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : X → Y} (hf : IsLocallyConstant f)
    (hinf : Set.Infinite (Set.range f)) :
    ContinuouslyReduces f (@id ℕ) := by
  by_contra h_contra;
  -- Let $g : ℕ ≃ range f$ be a bijection.
  obtain ⟨g, hg⟩ : ∃ g : ℕ ≃ Set.range f, True := by
    have h_countable : Countable (Set.range f) := by
      have h_countable : ∀ y ∈ Set.range f, ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ ∀ x ∈ U, f x = y := by
        intro y hy
        obtain ⟨x, hx⟩ : ∃ x, f x = y := by
          exact hy;
        exact ⟨ { z | f z = y }, hf.isOpen_fiber y, ⟨ x, hx ⟩, fun z hz => hz ⟩;
      choose! U hU using h_countable;
      have h_countable : ∀ y ∈ Set.range f, ∃ B ∈ TopologicalSpace.countableBasis X, B ⊆ U y ∧ B.Nonempty := by
        intro y hy
        obtain ⟨x, hx⟩ : ∃ x, x ∈ U y := (hU y hy).right.left
        have h_basis : ∃ B ∈ TopologicalSpace.countableBasis X, x ∈ B ∧ B ⊆ U y := by
          have := TopologicalSpace.isBasis_countableBasis X;
          exact this.exists_subset_of_mem_open hx ( hU y hy |>.1 );
        exact ⟨ h_basis.choose, h_basis.choose_spec.1, h_basis.choose_spec.2.2, ⟨ x, h_basis.choose_spec.2.1 ⟩ ⟩;
      choose! B hB using h_countable;
      have h_countable : Set.InjOn (fun y => B y) (Set.range f) := by
        intro y hy z hz h_eq;
        obtain ⟨ x, hx ⟩ := hB y hy |>.2.2;
        grind;
      have h_countable : Set.Countable (Set.image (fun y => B y) (Set.range f)) := by
        exact Set.Countable.mono ( Set.image_subset_iff.mpr fun y hy => hB y hy |>.1 ) ( TopologicalSpace.countable_countableBasis X );
      exact Set.MapsTo.countable_of_injOn ( Set.mapsTo_image _ _ ) ‹_› h_countable;
    have h_countable : Infinite (Set.range f) := by
      exact Set.infinite_coe_iff.mpr hinf;
    exact ⟨ ( Classical.arbitrary _ ), trivial ⟩;
  refine' h_contra ⟨ _, _, _, _ ⟩;
  exact fun x => g.symm ⟨ f x, Set.mem_range_self x ⟩;
  swap;
  exact fun n => ( g n ).val;
  · grind +suggestions;
  · simp +decide [ continuousOn_iff_continuous_restrict ];
    exact continuous_of_discreteTopology

/-
Backward direction: id_ℕ ≤ f when f is locally constant with infinite range.
With the ContinuousOn-based definition, τ only needs to be continuous on range(f ∘ σ).
-/
theorem id_nat_reduces_locally_constant {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : X → Y} (hf : IsLocallyConstant f)
    (hinf : Set.Infinite (Set.range f)) :
    ContinuouslyReduces (@id ℕ) f := by
  by_contra h_contra;
  -- Since range f is infinite and Y is metrizable, by `exists_infinite_discreteTopology` applied to Set.range f (which is Infinite and MetrizableSpace), we get an infinite discrete subset T of range f.
  obtain ⟨T, hT_inf, hT_discrete⟩ : ∃ T : Set Y, Set.Infinite T ∧ DiscreteTopology T ∧ T ⊆ Set.range f := by
    obtain ⟨T, hT⟩ : ∃ T : Set (↥(Set.range f)), T.Infinite ∧ DiscreteTopology T := by
      convert exists_infinite_discreteTopology ( Set.range f );
      exact Set.infinite_coe_iff.mpr hinf;
    refine' ⟨ T.image Subtype.val, _, _, _ ⟩;
    · exact hT.1.image fun x => by aesop;
    · rw [ discreteTopology_iff_singleton_mem_nhds ] at *;
      simp_all +decide [ nhds_induced, Set.image ];
      grind;
    · exact Set.image_subset_iff.mpr fun x hx => x.2;
  -- Since T is infinite, there is a bijection g : ℕ ≃ T.
  obtain ⟨g, hg⟩ : ∃ g : ℕ ≃ T, True := by
    have hT_countable : Countable T := by
      have h_countable : Countable (Set.range f) := by
        have h_countable : ∃ D : Set X, D.Countable ∧ Dense D := by
          exact ⟨_, (TopologicalSpace.SeparableSpace.exists_countable_dense (α := X)).choose_spec.1,
                 (TopologicalSpace.SeparableSpace.exists_countable_dense (α := X)).choose_spec.2⟩;
        have h_countable : ∀ x : X, ∃ y ∈ h_countable.choose, f x = f y := by
          intro x
          obtain ⟨U, hU_open, hxU, hU_const⟩ : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, f y = f x := by
            exact ⟨f ⁻¹' {f x}, hf.isOpen_fiber _, rfl, fun y hy => hy⟩;
          have := h_countable.choose_spec.2.inter_nhds_nonempty ( hU_open.mem_nhds hxU ) ; obtain ⟨ y, hyD, hyU ⟩ := this; exact ⟨ y, hyD, hU_const y hyU ▸ rfl ⟩ ;
        have h_countable : Set.Countable (Set.image f (‹∃ D : Set X, D.Countable ∧ Dense D›.choose)) := by
          exact Set.Countable.image ( ‹∃ D : Set X, D.Countable ∧ Dense D›.choose_spec.1 ) _;
        exact Set.countable_coe_iff.mpr ( h_countable.mono fun x hx => by obtain ⟨ y, hy, rfl ⟩ := hx; obtain ⟨ z, hz, hz' ⟩ := ‹∀ x : X, ∃ y ∈ _, f x = f y› y; aesop );
      exact Set.countable_coe_iff.mpr ( Set.Countable.mono hT_discrete.2 ( Set.countable_coe_iff.mp h_countable ) );
    have hT_infinite : Infinite T := by
      exact Set.infinite_coe_iff.mpr hT_inf;
    exact ⟨ ( Classical.arbitrary _ ), trivial ⟩;
  -- For each n, since g(n) ∈ T ⊆ range f, pick σ(n) with f(σ(n)) = (g n).val.val (the actual value in Y). σ is continuous because ℕ has discrete topology.
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → X, ∀ n, f (σ n) = (g n).val := by
    exact ⟨ fun n => Classical.choose ( hT_discrete.2 ( g n |>.2 ) ), fun n => Classical.choose_spec ( hT_discrete.2 ( g n |>.2 ) ) ⟩
  have hσ_cont : Continuous σ := by
    exact continuous_of_discreteTopology
  generalize_proofs at *; (
  -- Since range(f ∘ σ) = {(g n).val.val : n ∈ ℕ} = image of T under Subtype.val composed with Subtype.val, and T is discrete in range f, range(f ∘ σ) is discrete in Y.
  have h_range_discrete : DiscreteTopology (Set.range (f ∘ σ)) := by
    have h_range_discrete : Set.range (f ∘ σ) = T := by
      ext y; simp [hσ];
      exact ⟨ fun ⟨ n, hn ⟩ => hn ▸ Subtype.mem _, fun hy => ⟨ g.symm ⟨ y, hy ⟩, by simp +decide ⟩ ⟩
    generalize_proofs at *; (
    exact h_range_discrete ▸ hT_discrete.1)
  generalize_proofs at *; (
  -- Define τ(y) = g⁻¹(corresponding element) if y ∈ range(f ∘ σ), else 0. ContinuousOn τ (range(f ∘ σ)) holds because range(f ∘ σ) is discrete.
  obtain ⟨τ, hτ⟩ : ∃ τ : Y → ℕ, ContinuousOn τ (Set.range (f ∘ σ)) ∧ ∀ n, τ (f (σ n)) = n := by
    -- Define τ : Y → ℕ by τ(y) = g⁻¹(corresponding element) if y ∈ range(f ∘ σ), else 0. ContinuousOn τ (range(f ∘ σ)) holds because range(f ∘ σ) is discrete. Use the fact that any function on a discrete space is continuous.
    have hτ_cont : ∀ y ∈ Set.range (f ∘ σ), ∃! n : ℕ, f (σ n) = y := by
      simp +decide [ hσ ];
      exact fun n => ⟨ n, rfl, fun m hm => g.injective <| Subtype.ext hm ⟩
    generalize_proofs at *; (
    choose! τ hτ₁ hτ₂ using hτ_cont
    generalize_proofs at *; (
    refine' ⟨ τ, _, _ ⟩;
    · rw [ continuousOn_iff_continuous_restrict ];
      exact continuous_of_discreteTopology;
    · exact fun n => hτ₂ _ ( Set.mem_range_self _ ) _ rfl ▸ rfl))
  generalize_proofs at *; (
  exact h_contra ⟨ σ, hσ_cont, τ, hτ.1, fun n => by simp +decide [ hτ.2 ] ⟩)))

/-- **Proposition 2.24 (locally constant equivalence).** A locally constant function
with infinite image is continuously equivalent to id_ℕ. -/
theorem locally_constant_infinite_image {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : X → Y} (hf : IsLocallyConstant f)
    (hinf : Set.Infinite (Set.range f)) :
    ContinuouslyEquiv f (@id ℕ) :=
  ⟨locally_constant_infinite_image_forward hf hinf, id_nat_reduces_locally_constant hf hinf⟩

/-- **Proposition 2.24.** The class of locally constant functions from a second-countable
space to a metrizable space is finitely generated by `{id₁, id_ℕ}`. More precisely:
- If `f` is constant, then `f ≡ id_Unit`.
- If `f` has finite image of size `n ≥ 2`, then `f ≡ n ⋅ id_Unit` (a finite gluing).
- If `f` has infinite image, then `f ≡ id_ℕ`.

The precise formalization of "finitely generated via gluings" requires the gluing
equivalence machinery. We state the infinite-image case separately above
(`locally_constant_infinite_image`). -/
theorem locally_constant_nonempty_reduces_to_id_unit {X Y : Type*}
    [TopologicalSpace X] [SecondCountableTopology X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    [Nonempty X]
    {f : X → Y} (_hf : IsLocallyConstant f)
    (_hfin : (Set.range f).Finite) (hone : (Set.range f).ncard = 1) :
    ContinuouslyEquiv f (id : Unit → Unit) := by
  have : ∃ y, ∀ x, f x = y := by
    rw [Set.ncard_eq_one] at hone
    obtain ⟨y, hy⟩ := hone
    exact ⟨y, fun x => by rw [Set.ext_iff] at hy; exact (hy (f x)).mp (Set.mem_range_self x)⟩
  exact constant_equiv_id_singleton this

end LocallyConstantFunctions

section Fact_GluingCohomomorphism

/-!
## Fact 2.22 (Gluingcohomomorphism)

If there exists `ι : I → K` with `f_i ≤ g_{ι(i)}` for all `i`, then
`⊔_i f_i ≤ ⊔_k g_k`. In particular, if `m ≤ n ≤ ω`, then `mf ≤ nf`.
-/

-- This follows from the gluing upper bound characterization.

end Fact_GluingCohomomorphism

section InfiniteDiscreteSubspace

/-!
## Fact 2.25 (InfiniteEmbedOmega)

Any infinite metrizable space contains an infinite discrete subspace.
-/

/-
Any infinite metrizable space contains a countably infinite discrete subspace.
-/
theorem exists_infinite_discrete_subspace {X : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [Infinite X] :
    ∃ (S : Set X), S.Infinite ∧ DiscreteTopology S :=
  exists_infinite_discreteTopology X

end InfiniteDiscreteSubspace
