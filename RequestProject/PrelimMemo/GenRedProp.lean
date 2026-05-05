import RequestProject.PrelimMemo.Basic

open scoped Topology
open Set Function TopologicalSpace

set_option maxHeartbeats 4000000

/-!
# Baire open reduction (relative version)

We prove that for any subspace `A` of the Baire space `ℕ → ℕ`,
any countable family of open sets `U n` in `A` can be "reduced" to
a pairwise-disjoint family of open sets `V n` with `V n ⊆ U n`
and `⋃ V n = ⋃ U n`.

The proof goes through a clopen decomposition in the zero-dimensional Baire space.
-/

section ClopenBasis

def nbhd (x : Baire) (n : ℕ) : Set Baire :=
  {h : Baire | ∀ i ∈ Finset.range n, h i = x i}

/-- neighborhood of a point in the Baire space is clopen -/
lemma baire_nbhd_isClopen (x : Baire) (n : ℕ) :
    IsClopen (nbhd x n) := by
  -- Rewrite as a finite intersection
  have h_eq : nbhd x n = ⋂ i ∈ Finset.range n, {h : Baire | h i = x i} := by
    ext h
    simp [nbhd]
  rw [h_eq]

  -- PROOF 1: The intersection is Closed
  have h_closed : IsClosed (⋂ i ∈ Finset.range n, {h : Baire | h i = x i}) := by
    apply isClosed_biInter
    intro i _
    exact isClosed_eq (continuous_apply i) continuous_const

  -- PROOF 2: The intersection is Open
  have h_open : IsOpen (⋂ i ∈ Finset.range n, {h : Baire | h i = x i}) := by
    apply Set.Finite.isOpen_biInter (Finset.finite_toSet ( Finset.range n ) );
    intro i _
    have h_preimage : {h : Baire | h i = x i} = (fun h => h i) ⁻¹' {x i} := rfl
    rw [ isOpen_pi_iff ];
    exact fun h hf => ⟨ { i }, fun _ => { x i }, by aesop ⟩
  -- Combine them explicitly (IsClopen is defined as IsClosed ∧ IsOpen)
  exact ⟨h_closed, h_open⟩

  

/-
In the Baire space ℕ → ℕ, the set `{f | f i = a}` is clopen for every `i a : ℕ`.
-/
lemma baire_fiber_isClopen (i a : ℕ) :
    IsClopen {f : ℕ → ℕ | f i = a} := by
  constructor;
  · exact isClosed_eq ( continuous_apply i ) continuous_const;
  · rw [ isOpen_pi_iff ];
    exact fun f hf => ⟨ { i }, fun _ => { a }, by aesop ⟩

/-
A cylinder set (finite intersection of fibers) in the Baire space is clopen.
-/
lemma baire_cylinder_isClopen (s : Finset ℕ) (g : ℕ → ℕ) :
    IsClopen {f : ℕ → ℕ | ∀ i ∈ s, f i = g i} := by
  induction s using Finset.induction <;> simp_all +decide [ Set.setOf_and ];
  · exact isClopen_univ
  · exact IsClopen.inter (baire_fiber_isClopen _ _) ‹_›

/-
Singletons form a topological basis for the discrete topology on ℕ.
-/
lemma nat_singleton_basis :
    IsTopologicalBasis {s : Set ℕ | ∃ n, s = {n}} := by
  refine' isTopologicalBasis_of_isOpen_of_nhds _ _;
  · aesop;
  · exact fun a u ha hu => ⟨ { a }, ⟨ a, rfl ⟩, by simp, by simpa ⟩

/-
The Baire space has a topological basis consisting of clopen sets.
-/
lemma baire_has_clopen_basis :
    ∃ B : Set (Set (ℕ → ℕ)), IsTopologicalBasis B ∧ B.Countable ∧ ∀ s ∈ B, IsClopen s := by
  refine' ⟨ _, _, _, _ ⟩;
  refine' { s : Set ( ℕ → ℕ ) | ∃ ( F : Finset ℕ ) ( g : ℕ → ℕ ), s = { f : ℕ → ℕ | ∀ i ∈ F, f i = g i } };
  · refine' isTopologicalBasis_of_isOpen_of_nhds _ _;
    · simp +zetaDelta at *;
      intro u F g hu; rw [ hu ] ; exact baire_cylinder_isClopen F g |>.isOpen;
    · intro a u ha hu;
      rw [ isOpen_pi_iff ] at hu;
      obtain ⟨ I, u, hu₁, hu₂ ⟩ := hu a ha;
      refine' ⟨ _, ⟨ I, a, rfl ⟩, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  · -- The set of finite subsets of ℕ is countable.
    have h_finite_subsets_countable : Set.Countable {F : Finset ℕ | True} := by
      exact Set.countable_univ;
    refine' Set.Countable.mono _ ( h_finite_subsets_countable.biUnion fun F _ => Set.countable_range ( fun g : F → ℕ => { f : ℕ → ℕ | ∀ i : F, f i = g i } ) );
    intro s hs; obtain ⟨ F, g, rfl ⟩ := hs; simp +decide [ Set.ext_iff ] ;
    exact ⟨ F, fun i => g i, fun x => ⟨ fun h i hi => h i hi, fun h i hi => h i hi ⟩ ⟩;
  · rintro s ⟨ F, g, rfl ⟩ ; exact baire_cylinder_isClopen F g;

/-
In the Baire space, every open set is a countable union of clopen sets.
-/
lemma baire_open_eq_countable_union_clopen {U : Set (ℕ → ℕ)} (hU : IsOpen U) :
    ∃ C : ℕ → Set (ℕ → ℕ), (∀ k, IsClopen (C k)) ∧ U = ⋃ k, C k := by
  obtain ⟨ B, hB₁, hB₂, hB₃ ⟩ := baire_has_clopen_basis;
  have h_union : U = ⋃₀ { s ∈ B | s ⊆ U } := by
    exact hB₁.open_eq_sUnion' hU
  have h_countable : Set.Countable { s ∈ B | s ⊆ U } := by
    exact hB₂.mono fun s hs => hs.1;
  have := h_countable.exists_eq_range;
  by_cases h : { s ∈ B | s ⊆ U }.Nonempty;
  · obtain ⟨ f, hf ⟩ := this h;
    refine' ⟨ f, _, _ ⟩;
    · exact fun k => hB₃ _ <| hf.symm.subset ( Set.mem_range_self k ) |>.1;
    · convert h_union using 1;
      simp +decide [ hf];
  · simp_all +singlePass [ Set.not_nonempty_iff_eq_empty ];
    exact ⟨ fun _ => ∅, fun _ => by simp +decide [ IsClopen ], by simp +decide ⟩

/-
In any subspace of the Baire space, every open set is a countable union of
    sets that are clopen in the subspace.
-/
lemma subspace_open_eq_countable_union_clopen (A : Set (ℕ → ℕ))
    {U : Set A} (hU : IsOpen U) :
    ∃ C : ℕ → Set A, (∀ k, IsClopen (C k)) ∧ U = ⋃ k, C k := by
  obtain ⟨V, hV⟩ : ∃ V : Set (ℕ → ℕ), IsOpen V ∧ U = Subtype.val ⁻¹' V := by
    obtain ⟨ V, hV₁, hV₂ ⟩ := hU;
    exact ⟨ V, hV₁, hV₂.symm ⟩;
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Set (ℕ → ℕ), (∀ k, IsClopen (C k)) ∧ V = ⋃ k, C k := by
    exact baire_open_eq_countable_union_clopen hV.1;
  use fun k => Subtype.val ⁻¹' C k;
  simp_all +decide [ Set.ext_iff ];
  intro k; specialize hC; have := hC.1 k; exact ⟨ this.1.preimage continuous_subtype_val, this.2.preimage continuous_subtype_val ⟩ ;

end ClopenBasis

section DisjointedClopen

/-
The `disjointed` of a sequence of clopen sets is clopen.
-/
lemma disjointed_clopen {X : Type*} [TopologicalSpace X]
    (f : ℕ → Set X) (hf : ∀ n, IsClopen (f n)) (n : ℕ) :
    IsClopen (disjointed f n) := by
  convert IsClopen.diff ( hf n ) _;
  induction' ( Finset.Iio n ) using Finset.induction <;> simp_all +decide [ Finset.sup_insert];
  · exact isClopen_empty;
  · exact IsClopen.union ( hf _ ) ‹_›

end DisjointedClopen

section MainTheorem

/-
The generalized reduction property for open sets relative to an arbitrary subspace A.
-/
theorem baire_open_reduction_rel
    (A : Set Baire)
    (U : ℕ → Set A)
    (hU_open : ∀ n, IsOpen (U n)) :
    ∃ V : ℕ → Set A,
      (∀ n, IsOpen (V n)) ∧
      (∀ n, V n ⊆ U n) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
      (⋃ n, V n = ⋃ n, U n) := by
  -- STEP 1: Decompose each U n into clopen sets
  have h_clopen_decomp : ∃ C : ℕ → ℕ → Set A,
      (∀ n k, IsClopen (C n k)) ∧ (∀ n, U n = ⋃ k, C n k) := by
    have h := fun n => subspace_open_eq_countable_union_clopen A (hU_open n)
    choose C hC using h
    exact ⟨C, fun n k => (hC n).1 k, fun n => (hC n).2⟩
  obtain ⟨C, hC_clopen, hC_union⟩ := h_clopen_decomp
  -- STEP 2: Flatten the double sequence
  let C_flat : ℕ → Set A := fun m => C (Nat.unpair m).1 (Nat.unpair m).2
  -- STEP 3: Disjointify
  let D : ℕ → Set A := disjointed C_flat
  -- STEP 4: Reassemble
  let V : ℕ → Set A := fun n => ⋃ (m : ℕ) (_ : (Nat.unpair m).1 = n), D m
  use V
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- V n is open (union of clopen sets)
    intro n
    apply isOpen_iUnion; intro m
    apply isOpen_iUnion; intro _
    exact (disjointed_clopen C_flat (fun m => hC_clopen _ _) m).2
  · -- V n ⊆ U n
    intro n x hx
    simp only [V, Set.mem_iUnion] at hx
    obtain ⟨m, hm, hxD⟩ := hx
    have hxC : x ∈ C_flat m := disjointed_subset _ _ hxD
    rw [hC_union n]
    simp only [C_flat] at hxC
    rw [hm] at hxC
    exact Set.mem_iUnion.mpr ⟨(Nat.unpair m).2, hxC⟩
  · -- V i and V j are disjoint
    intro i j hij
    simp only [V, Set.disjoint_iff]
    intro x ⟨hi, hj⟩
    simp only [Set.mem_iUnion] at hi hj
    obtain ⟨mi, hmi, hxDi⟩ := hi
    obtain ⟨mj, hmj, hxDj⟩ := hj
    have h_mi_ne_mj : mi ≠ mj := by
      intro h_eq; rw [h_eq] at hmi; exact hij (hmi ▸ hmj)
    exact Set.disjoint_iff.mp
      (disjoint_disjointed C_flat h_mi_ne_mj) ⟨hxDi, hxDj⟩
  · -- ⋃ V n = ⋃ U n
    have h_union_D : ⋃ m, D m = ⋃ n, U n := by
      rw [ iUnion_disjointed ];
      ext x; simp [C_flat, hC_union];
      exact ⟨ fun ⟨ m, hm ⟩ => ⟨ _, _, hm ⟩, fun ⟨ n, k, hk ⟩ => ⟨ Nat.pair n k, by simpa using hk ⟩ ⟩;
    convert h_union_D using 1;
    ext x; simp [V]

end MainTheorem
