import Mathlib
import RequestProject.PrelimMemo.Gluing
open scoped Topology
open Set Function TopologicalSpace

/-- The constant zero sequence `0^ω ∈ ℕ → ℕ`. -/
def zeroStream : ℕ → ℕ := fun _ => 0

abbrev Baire := ℕ → ℕ

theorem gluingFun_upper_bound_backward_
    -- tell Lean Baire is a topological space
    -- so that subets inherit the subspace topology
    [TopologicalSpace Baire]
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
    let gl := (fun (x : GluingSet A) => (GluingFunVal A B gi x))
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
    let σ (x : D) : (GluingSet A) := by
      -- First, x is trivially in the universal set. By rewriting hcover backwards,
      -- we prove x is in the union of all P i.
      have hx_union : x.val ∈ ⋃ i, P i := by
              rw [hcover]
              exact x.property -- extracts the proof that x ∈ S
      -- so it belongs to some P_i
      have h_exists : ∃ i, x.val ∈ P i := Set.mem_iUnion.mp hx_union
      -- 1. Get the index `i` using the Axiom of Choice
      let i := Classical.choose h_exists
      -- 2. Get the proof that `x ∈ P i`
      have hi : x.val ∈ P i := Classical.choose_spec h_exists
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
    let σ_raw : D → Baire := fun x => (σ x).val
    let σ_prop  := fun x => (σ x).val


    -- σ is well-defined (remove the use of choice)
    have h_choose_eq (i : ℕ) (x : D) (hx_union : x.val ∈ ⋃ j, P j) (hx : x.val ∈ P i) :
        (Classical.choose (Set.mem_iUnion.mp hx_union)) = i := by
      let j := Classical.choose (Set.mem_iUnion.mp hx_union)
      have hj : x.val ∈ P j := Classical.choose_spec (Set.mem_iUnion.mp hx_union)
      by_contra h_neq
      have h_disjoint := hdisj j i h_neq
      have h_not_in_i := Set.disjoint_left.mp h_disjoint hj
      exact h_not_in_i hx

    have hσ_cont_piece (i : ℕ) : ContinuousOn σ {x : D | x.val ∈ P i} := by
      rw [continuousOn_iff_continuous_restrict]

      -- Bridge the gap between the bundled GluingSet A and the raw Baire sequence
      apply continuous_induced_rng.mpr
      -- 3. THE RAW DEFINITIONS

      have h_eq : ({w : D | w.val ∈ P i}).restrict σ_raw =
                  (fun (x : {w : D // w.val ∈ P i}) => prepend i (σ_choose i ⟨x.val.val, x.property⟩)) := by
        sorry
        -- ext x
        -- -- Extract the exact proofs we need for the specific x
        -- have hx_in_Pi : x.val.val ∈ P i := x.property
        -- have hx_union : x.val.val ∈ ⋃ j, P j := by
        --   rw [hcover]
        --   exact x.val.property

        -- -- Unfold definitions so Lean can see the Classical.choose
        -- unfold σ_raw σ

        -- -- Use simp instead of rw. `simp` is much better at applying lemmas
        -- -- even when the invisible proof terms look slightly different.
        -- simp only [h_choose_eq i x.val hx_union hx_in_Pi]

      -- Swap out the messy choose function for your clean, continuous formula
      -- rw [h_eq]

      -- Apply continuity!
      -- exact Continuous.comp (continuous_prepend i) (hσ_choose i)

    -- have hσ_range : ∀ x : D, σ x ∈ GluingSet A := by
    --   intro x
    --   have h_mem : σ x ∈ GluingSet A := by
    --     -- GluingSet A is defined as ⋃ i, prepend i '' (A i).
    --     -- We show it belongs to the i-th piece of the union.
    --     apply Set.mem_iUnion.mpr
    --     use i

    --     -- We now need to show `raw_y` is in the image `prepend i '' (A i)`.
    --     -- Since `y_.val` is in `A i` (which is exactly `y_.property`), this is true!
    --     exact Set.mem_image_of_mem (prepend i) y_.property
    --   -- Now your goal is to prove `σ x ∈ GluingSet A`
    --   sorry
      sorry

      -- 5. Return the bundled subtype ⟨sequence, proof⟩

    let τ (z : ℕ → ℕ) : Baire := by
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

          -- 3. Feed the tail
        exact τ_choose i (unprepend z)

      else
        exact zeroStream
    -- show that σ and τ are continuous on their domain
    -- σ is continuous
    -- Define the raw version
    let σ_raw : D → Baire := fun x => (σ x).val
    let σ_prop := fun x => (σ x).property

    have σ_cont : Continuous σ := by sorry
    have τ_cont : ContinuousOn τ (Set.range (gl ∘ σ)):= by sorry
    have red_eq : ∀ x : D, f x = τ (gl (σ x)) := by sorry

    exact ⟨σ, σ_cont, τ, τ_cont, red_eq⟩

    -- have hσ_cont_piece (i : ℕ) : ContinuousOn σ {x : D | x.val ∈ P i} := by
    --   -- 1. Convert ContinuousOn into standard Continuous on the restricted subtype domain.
    --   rw [continuousOn_iff_continuous_restrict]

    --   -- 2. State that our restricted raw sequence function is exactly equal to the continuous formula.
    --   have h_eq : ({w : D | w.val ∈ P i}).restrict σ_raw =
    --               (fun (x : {w : D // w.val ∈ P i}) => prepend i (σ_choose i ⟨x.val.val, x.property⟩)) := by
    --     ext x
    --     -- Step A: Unfold restrict, σ_raw, and σ to expose the Classical.choose algorithm
    --     dsimp only [Set.restrict, σ_raw, σ_prop]
    --     #check σ_raw
    --     -- Step B: Extract the exact proofs that your h_choose_eq lemma demands
    --     have hx_in_Pi : x.val.val ∈ P i := x.property
    --     have hx_union : x.val.val ∈ ⋃ j, P j := by
    --       rw [hcover]
    --       exact x.val.property

    --     -- Step C: Force the chosen index to become `i`
    --     --  (i : ℕ) (x : D) (hx_union : x.val ∈ ⋃ i, P i) (hx : x.val ∈ P i) :
    --     -- (Classical.choose (Set.mem_iUnion.mp  hx_union)) = i
    --       have index_eq: (Classical.choose (Set.mem_iUnion.mp  hx_union)) = i := by exact h_choose_eq i x.val hx_union hx_in_Pi

    --   -- 3. BRIDGE THE GAP: Convert the goal from bundled σ to the raw sequence σ_raw
    --   -- Mathlib's continuous_induced_rng.mpr says "a function into a subtype is continuous
    --   -- if and only if its composition with .val is continuous".
    --   apply continuous_induced_rng.mpr

    --   -- 4. Now the goal perfectly matches h_eq! Swap it out.
    --   rw [h_eq]

    --   -- 5. Now that the opaque Classical.choose is gone, apply your continuity lemmas!
    --   exact Continuous.comp (continuous_prepend i) (hσ_choose i)
    -- show the equality
