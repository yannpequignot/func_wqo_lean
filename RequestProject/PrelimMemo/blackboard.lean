import Mathlib
import RequestProject.PrelimMemo.Gluing
open scoped Topology
open Set Function TopologicalSpace


theorem gluingFun_upper_bound_backward
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y}
    {A : ℕ → Set (ℕ → ℕ)} {B : ℕ → Set (ℕ → ℕ)}
    {gi : ∀ i, A i → B i}
    (P : ℕ → Set X)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = univ)
    (hred : ∀ i, ContinuouslyReduces (f ∘ (Subtype.val : P i → X))
      (fun (a : A i) => (gi i a).val)) :
    ContinuouslyReduces f (fun (x : GluingSet A) => (GluingFunVal A B gi x)) := by
    -- 1. Create the family of functions σ : i ↦ σ_i
    let σ := fun i => Classical.choose (hred i)

    -- Cache the rest of the proof family so we don't recalculate it
    have h_rest := fun i => Classical.choose_spec (hred i)

    -- Extract the family of continuity proofs for σ
    have hσ := fun i => (h_rest i).1

    -- 2. Create the family of functions τ : i ↦ τ_i
    let τ := fun i => Classical.choose (h_rest i).2

    -- Cache the innermost proof family
    have h_rest2 := fun i => Classical.choose_spec (h_rest i).2

    -- Extract the family of continuity proofs for τ and the equality proofs
    have hτ := fun i => (h_rest2 i).1
    have heq := fun i => (h_rest2 i).2
    sorry
