import Mathlib
import RequestProject.PrelimMemo.Gluing
open scoped Topology
open Set Function TopologicalSpace

/-- The constant zero sequence `0^ω ∈ ℕ → ℕ`. -/
def zeroStream : ℕ → ℕ := fun _ => 0

abbrev Baire := ℕ → ℕ

theorem gluingFun_upper_bound_backward_
    [TopologicalSpace Baire]   -- ADD THIS LINE!
    {f : Baire → Baire}
    {D : Set Baire}  -- Your domain subset!
    {A : ℕ → Set Baire} {B : ℕ → Set Baire}
    {gi : ∀ i, A i → B i}
    (P : ℕ → Set Baire)
    (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : (⋃ i, P i) = D)
    (hred : ∀ i, ContinuouslyReduces ((P i).restrict f) (fun (a : A i) => (gi i a).val)) :
    ContinuouslyReduces (D.restrict f) (fun (x : GluingSet A) => (GluingFunVal A B gi x)) := by
    -- 1. Create the family of functions σ : i ↦ σ_i
    let σ_choose := fun i => Classical.choose (hred i)

    -- Cache the rest of the proof family so we don't recalculate it
    have h_rest := fun i => Classical.choose_spec (hred i)

    -- Extract the family of continuity proofs for σ
    have hσ_choose := fun i => (h_rest i).1

    -- 2. Create the family of functions τ : i ↦ τ_i
    let τ_choose := fun i => Classical.choose (h_rest i).2

    -- Cache the innermost proof family
    have h_rest2 := fun i => Classical.choose_spec (h_rest i).2

    -- Extract the family of continuity proofs for τ and the equality proofs
    have hτ := fun i => (h_rest2 i).1
    have heq := fun i => (h_rest2 i).2
    have σ (x : D) : (GluingSet A) := by
      -- First, x is trivially in the universal set. By rewriting hcover backwards,
      -- we prove x is in the union of all P i.
      have hx_union : ↑x ∈ ⋃ i, P i := by
              rw [hcover]
              exact x.property -- extracts the proof that x ∈ S
      -- so it belongs to some P_i
      have h_exists : ∃ i, ↑x ∈ P i := Set.mem_iUnion.mp hx_union
      -- 1. Get the index `i` using the Axiom of Choice
      let i := Classical.choose h_exists
      -- 2. Get the proof that `x ∈ P i`
      have hi : ↑x ∈ P i := Classical.choose_spec h_exists
      let y_ := σ_choose i ⟨x, hi⟩
      let raw_y := prepend i y_.val
      have h_mem : raw_y ∈ GluingSet A := by
        -- GluingSet A is defined as ⋃ i, prepend i '' (A i).
        -- We show it belongs to the i-th piece of the union.
        apply Set.mem_iUnion.mpr
        use i

        -- We now need to show `raw_y` is in the image `prepend i '' (A i)`.
        -- Since `y_.val` is in `A i` (which is exactly `y_.property`), this is true!
        exact Set.mem_image_of_mem (prepend i) y_.property
      -- 5. Return the bundled subtype ⟨sequence, proof⟩
      exact ⟨raw_y, h_mem⟩

    have τ (z : ℕ → ℕ) : Baire := by
      if h_in : z ∈ GluingSet B then
        -- 1. Get the first value
        let i := z 0

        -- 2. Prove the tail belongs to B i
        have hzi : unprepend z ∈ B i := by
          -- Extract j from the union
          have hz_exists : ∃ j, z ∈ prepend j '' (B j) := Set.mem_iUnion.mp h_in
          obtain ⟨j, hj⟩ := hz_exists

          -- Unpack the image set: there is some y in B j that maps to z
          -- hy_mem is the proof y ∈ B j
          -- hy_eq is the proof that (prepend j y = z)
          obtain ⟨y, hy_mem, hy_eq⟩ := hj

          -- Prove that i is actually equal to j
          have h_i_eq_j : i = j := by
            -- i is exactly `z 0`.
            -- Because z = prepend j y, `z 0` is just `j`!
            calc i = z 0 := rfl
                 _ = (prepend j y) 0 := by rw [← hy_eq]
                 _ = j := rfl

          -- Prove that the tail of z is exactly y
          have h_tail_eq_y : unprepend z = y := by
              -- First substitute z with (prepend j y), then apply your lemma
              rw [← hy_eq, unprepend_prepend]

          -- Now we just substitute `y` for `unprepend z`, and `j` for `i`
          rw [h_tail_eq_y, h_i_eq_j]
          exact hy_mem

          -- 3. Feed the tail (NOT z!) and the proof into the local function
        exact τ_choose i (unprepend z) -- ⟨unprepend z, hzi⟩

      else
        exact zeroStream
    -- show that σ and τ are continuous on their domain
    -- show the equality
    sorry
