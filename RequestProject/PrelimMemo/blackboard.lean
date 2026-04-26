import Mathlib.Topology.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Equiv.Nat
import Mathlib.Order.Disjointed
import RequestProject.PrelimMemo.Basic

/-- The generalized reduction property for open sets relative to an arbitrary subspace A. -/
theorem baire_open_reduction_rel
    (A : Set Baire)
    (U : ℕ → Set A)
    (hU_open : ∀ n, IsOpen (U n)) :
    ∃ V : ℕ → Set A,
      (∀ n, IsOpen (V n)) ∧
      (∀ n, V n ⊆ U n) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧
      (⋃ n, V n = ⋃ n, U n) := by
  -- STEP 1: Decompose each U n into a sequence of clopen sets C n k in the subspace A
  -- (Because A inherits its topology from a zero-dimensional space,
  -- it also has a basis of clopen sets in the relative topology)
  have h_clopen_decomp : ∃ C : ℕ → ℕ → Set A,
      (∀ n k, IsClopen (C n k)) ∧ (∀ n, U n = ⋃ k, C n k) := by
    sorry

  obtain ⟨C, hC_clopen, hC_union⟩ := h_clopen_decomp

-- STEP 2: Flatten the double sequence C n k into a single sequence
  -- Nat.unpair maps m to a tuple, so .1 gets 'n' and .2 gets 'k'
  let C_flat : ℕ → Set A := fun m => C (Nat.unpair m).1 (Nat.unpair m).2

  -- STEP 3: Disjointify the flat sequence
  let D : ℕ → Set A := disjointed C_flat

  -- STEP 4: Reassemble the disjointed pieces back into V n
  let V : ℕ → Set A := fun n => ⋃ (m : ℕ) (_ : (Nat.unpair m).1 = n), D m

  -- Provide V as the witness
  use V

  -- STEP 5: Prove the four properties
  refine ⟨?h_open, ?h_subset, ?h_disjoint, ?h_union⟩

  case h_open =>
    intro n
    -- D m is clopen in A, so V n is open in A
    sorry

  case h_subset =>
    intro n
    -- D m ⊆ C_flat m ⊆ U n
    sorry

  case h_disjoint =>
    intro i j h_neq
    -- Disjointness inherited directly from disjoint_disjointed
    sorry

  case h_union =>
    -- ⋃ n, V n = ⋃ m, D m = ⋃ m, C_flat m = ⋃ n, U n use iUnion_disjointed
    sorry
