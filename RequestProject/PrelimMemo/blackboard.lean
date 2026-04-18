import Mathlib

open scoped Topology
open Set Function TopologicalSpace



/-- The set of `f`-isolated points in a set `A`: points where `f|_A` is locally constant. -/
def isolatedLocus {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (A : Set X) : Set X :=
  {x ∈ A | ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ A, f y = f x}

theorem ContinuouslyReduces.scattered_local {X X' Y Y' : Type*}
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
