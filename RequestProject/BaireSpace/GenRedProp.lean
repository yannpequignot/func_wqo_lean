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
