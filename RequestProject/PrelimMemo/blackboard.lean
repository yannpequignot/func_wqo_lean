import Mathlib
import RequestProject.PrelimMemo.Scattered
open scoped Topology
open Set Function TopologicalSpace

theorem ContinuouslyReduces.scattered_local_ {X X' Y Y' : Type*}
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


-- -- 2. The Global Theorem using your Local Lemma
-- theorem ContinuouslyReduces.scattered__ {X X' Y Y' : Type*}
--     [TopologicalSpace X] [TopologicalSpace X']
--     [TopologicalSpace Y] [TopologicalSpace Y']
--     {f : X → Y} {g : X' → Y'}
--     (hred : f ≤ g) (hg : ScatteredFun g) :
--     ScatteredFun f := by
--   -- Let S be an arbitrary non-empty subset of X
--   intro S hS_nonempty

--   -- Unpack the reduction
--   rcases hred with ⟨σ, hσ, τ, hτ, heq⟩

--   -- Let A be the image of S, which is non-empty
--   let A : Set X' := σ '' S
--   have hA_nonempty : A.Nonempty := hS_nonempty.image σ

--   -- Since g is scattered, its isolated locus on A is non-empty
--   have hg_iso_nonempty : (isolatedLocus g A).Nonempty := hg A hA_nonempty

--   -- Extract a point 'y' from this non-empty isolated locus
--   obtain ⟨y, hy_iso⟩ := hg_iso_nonempty

--   -- Since y is in the isolated locus of A, it must be in A itself.
--   -- (isolatedLocus is a subset of A by definition)
--   obtain ⟨hy_in_A, _⟩ := hy_iso

--   -- Since y ∈ A and A = σ '' S, we can unpack y to find its preimage x in S
--   obtain ⟨x, hx_in_S, rfl⟩ := hy_in_A

--   -- Now we just apply your amazing local lemma!
--   have hx_iso : x ∈ isolatedLocus f S :=
--     scattered_local σ τ hσ hτ heq S x hx_in_S hy_iso

--   -- We found an isolated point for f in S, so the isolated locus is non-empty!
--   exact ⟨x, hx_iso⟩


theorem ContinuouslyReduces.scattered_ {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (hred : f ≤ g) (hg : ScatteredFun g) :
    ScatteredFun f := by
    obtain ⟨σ, hσ, τ, hτ, heq⟩ := hred;
    --obtain ⟨U, hUo, hyU, hU⟩ := hg;
    intro S hS -- let S be a nonempty subset of X
    #check hS
    let A : Set X' := σ '' S -- let A be the image of S by σ
    have hA_nonempty :A.Nonempty := hS.image σ -- A is non empty
    -- obtain ⟨x, hx⟩ := hS;

    -- have hsx : σ x ∈ σ '' S := by exact mem_image_of_mem σ hx; -- let x be a point in S

    -- now we use that g is scattered

    -- Step 1: Specialize the hypothesis to your set A

    have hg_A : ∃ U, IsOpen U ∧ (U ∩ A).Nonempty ∧ ∀ x ∈ U ∩ A, ∀ x' ∈ U ∩ A, g x = g x' := hg A hA_nonempty

    -- Step 2: Unpack the specialized hypothesis

    obtain ⟨U, hU_open, hU_nonempty, hg_const⟩ := hg_A

    -- obtain ⟨y, hy⟩ := hU_nonempty;

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
    have hx_in_isolatedLocus : (x ∈ isolatedLocus f S) := by exact ContinuouslyReduces.scattered_local σ τ hσ hτ heq S x hx_in_S hy_in_isolatedLocus
    obtain ⟨x_in_S, V, hVopen, hx_in_V, h_const_VS⟩ := hx_in_isolatedLocus
    have h_VS_nonempty : (V ∩ S).Nonempty := by exact ⟨x, hx_in_V, x_in_S⟩
    --  h_const_VS states that all points are mapped to the image of x under f
    -- what the definition of scattered requires is that any two points have the same image under f
    have hf_const_adapted : ∀ z ∈ V ∩ S, ∀ z' ∈ V ∩ S, f z = f z' := by
      intro z hz z' hz'
      -- Since f z = f x and f z' = f x, we can rewrite both to be f x
      rw [h_const_VS z hz, h_const_VS z' hz']
    exact ⟨V, hVopen, h_VS_nonempty, hf_const_adapted⟩
