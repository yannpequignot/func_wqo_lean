import RequestProject.PointedGluing.Theorems
import RequestProject.PointedGluing.MinFunHelpers

open scoped Topology
open Set Function TopologicalSpace Classical


set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Section 6: Pointed Gluing as a Lower Bound (Lemma 3.10, Proposition 3.11)
-/

/-- **Lemma (Pgluingaslowerbound).**
hclopen hypothesis is not used,
check the proof in the memoir to see
if we can drop this assumption-/
theorem pointedGluing_lower_bound_lemma'
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    (f : A → B)
    (C D : ℕ → Set (ℕ → ℕ))
    (g : ∀ n, C n → D n)
    (x : A)
    (An : ℕ → Set A)
    (hclopen : ∀ n, IsClopen (An n))
    (hsep : ∀ n, f x ∉ closure (f '' (An n)))
    (hpart : ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n)))
    (hpart_open : ∀ n, IsOpen (f '' (An n) : Set B))
    (hconv : SetsConvergeTo An x)
    (hred : ∀ n, ContinuouslyReduces
      (fun (z : C n) => (g n z : ℕ → ℕ))
      (f ∘ (Subtype.val : An n → A))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  -- Extract σ_n and τ_n from hred
  have hred' : ∀ n, ∃ (sn : C n → An n) (tn : B → ℕ → ℕ),
      Continuous sn ∧
      ContinuousOn tn (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ sn)) ∧
      ∀ z : C n, (g n z : ℕ → ℕ) = tn (f (sn z).val) := by
    intro n; obtain ⟨sn, hsn, tn, htn, heqn⟩ := hred n; exact ⟨sn, tn, hsn, htn, heqn⟩
  choose σ_n τ_n hσ_n hτ_n hτ_n_eq using hred'
  -- Define σ and τ
  let σ : PointedGluingSet C → A := fun z =>
    if h : z.val = zeroStream then x
    else (σ_n (firstNonzero z.val)
      ⟨stripZerosOne (firstNonzero z.val) z.val,
       strip_mem_of_pointedGluingSet C z h⟩).val
  let τ : B → ℕ → ℕ := fun y =>
    if h : ∃ n, y ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) then
      prependZerosOne (Classical.choose h) (τ_n (Classical.choose h) y)
    else zeroStream
  refine ⟨σ, ?_, τ, ?_, ?_⟩
  · -- Continuity of σ
    apply sufficient_cond_continuity σ {z : PointedGluingSet C | z.val ≠ zeroStream}
    · convert isClosed_singleton (x := (⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩ :
          PointedGluingSet C)).isOpen_compl using 1; ext z; simp [Subtype.ext_iff]
    · exact pgl_lower_bound_sigma_cont_on_U σ_n hσ_n
    · apply continuousOn_const.congr
      intro z hz; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
      exact (dif_pos hz : σ z = x)
    · intro z_k z₀ hz_k hz₀ hz_tendsto
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz₀
      exact pgl_lower_bound_sigma_seq σ_n hconv z_k z₀
        (fun n => (hz_k n : (z_k n).val ≠ zeroStream)) hz₀ hz_tendsto
  · -- ContinuousOn τ
    exact pgl_lower_bound_tau_cont σ_n τ_n hτ_n hsep hpart hpart_open
  · -- Equation
    exact pgl_lower_bound_equation σ_n τ_n hτ_n_eq hsep hpart


/-- **Proposition (Pgluingaslowerbound2). Pointed gluing as lower bound.** -/
theorem pointedGluing_lower_bound'
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (C D : ℕ → Set (ℕ → ℕ))
    (g : ∀ i, C i → D i)
    (x : A)
    (hloc : ∀ (i : ℕ) (U : Set A), IsOpen U → x ∈ U →
      ∃ (σ : C i → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
        Continuous σ ∧
        (∀ z, f (σ z) = τ (g i z)) ∧
        ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        f x ∉ closure (Set.range (fun z => f (σ z)))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  -- define basic neighborhoods at x and f(x)
  let cyl : ℕ → Set A := fun n =>
    Subtype.val ⁻¹' {h : ℕ → ℕ | ∀ i ∈ Finset.range n, h i = (x.val : ℕ → ℕ) i}

  have h_xincyl: ∀ n, x ∈ cyl n := fun n i _ => rfl

  -- Prove the cylinders are clopen in A by pulling back the clopen set from ℕ → ℕ
  have cyl_isClopen : ∀ n, IsClopen (cyl n) := by
    intro n
    have h_clopen_Baire := baire_cylinder_isClopen (Finset.range n) x.val
    exact h_clopen_Baire.preimage continuous_subtype_val

  let cylfx : ℕ → Set (ℕ → ℕ) := fun n =>
    {h : ℕ → ℕ | ∀ i ∈ Finset.range n, h i = (f x) i}

  -- This lemma isolates EXACTLY the mathematical induction step you described.
  have step_builder : ∀ (n : ℕ) (k : ℕ),
    ∃ (l m : ℕ) (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      Continuous σ ∧
      (∀ z, f (σ z) = τ (g n z)) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ cyl k) ∧
      Disjoint (closure (Set.range (fun z => f (σ z)))) (cylfx m) ∧
      f '' (cyl l) ⊆ cylfx m := by
    intro n k
    -- 1. Use hloc for U = cyl k (Extracting IsOpen from cyl_isClopen)
    have hcyl_open := (cyl_isClopen k).isOpen
    obtain ⟨σ, τ, hcont_σ, heq, hcont_τ, hin_k, hfx_not_in_closure⟩ :=
      hloc n (cyl k) hcyl_open (h_xincyl k)

    -- 2. Find m such that cylfx m is disjoint from the closure
    let closed_img := closure (Set.range (fun z => f (σ z)))
    have h_compl_open : IsOpen closed_imgᶜ := isClosed_closure.isOpen_compl
    have hfx_in_compl : f x ∈ closed_imgᶜ := hfx_not_in_closure

    -- Because `closed_imgᶜ` is open and contains `f x`, there exists a basic
    -- cylinder neighborhood around `f x` fully contained within it.
    have h_exists_m : ∃ m, cylfx m ⊆ closed_imgᶜ := by
      -- Replace with your Baire space basis lemma (e.g., `nhds_basis_cylinder`)
      sorry

    obtain ⟨m, hm_sub⟩ := h_exists_m

    -- Subsets of the complement are disjoint from the original set
    have hdisj : Disjoint closed_img (cylfx m) := by
      rw [Set.disjoint_left]
      intro y hy h_in_cyl
      exact hm_sub h_in_cyl hy

    -- 3. Find l such that f '' (cyl l) ⊆ cylfx m
    have h_cylfx_open : IsOpen (cylfx m) := (baire_cylinder_isClopen (Finset.range m) (f x)).isOpen
    have h_preimage_open : IsOpen (f ⁻¹' (cylfx m)) := h_cylfx_open.preimage hf

    have hx_in_preimage : x ∈ f ⁻¹' (cylfx m) := by
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro i _
      rfl

    -- Because `f ⁻¹' (cylfx m)` is open in A and contains `x`,
    -- there exists a basic cylinder neighborhood around `x` contained within it.
    have h_exists_l : ∃ l, cyl l ⊆ f ⁻¹' (cylfx m) := by
      -- Replace with your Baire space basis lemma
      sorry

    obtain ⟨l, hl_sub⟩ := h_exists_l

    -- Translate preimage subset to image subset
    have hfl_sub : f '' (cyl l) ⊆ cylfx m := Set.image_subset_iff.mpr hl_sub

    exact ⟨l, m, σ, τ, hcont_σ, heq, hcont_τ, hin_k, hdisj, hfl_sub⟩

  -- Now we do the Lean wiring.
  -- Notice we don't need a structure! `choose` will automatically create separate
  -- functions for l, m, σ, and τ, along with functions for all their proofs.
  choose next_l next_m next_σ next_τ h_cont heq hτ_cont hin_k hdisj hfl_sub using step_builder

  -- We recursively define the sequence of k values using Nat.recOn to avoid asyncDecl panics.
  -- k_0 is 0. k_{n+1} is exactly the `next_l` chosen from step n.
  let k_seq : ℕ → ℕ := fun n =>
    Nat.recOn n 0 (fun idx prev_k => next_l idx prev_k)

  -- ... [previous wiring code] ...
  let l_seq : ℕ → ℕ := fun n => next_l n (k_seq n)
  let m_seq : ℕ → ℕ := fun n => next_m n (k_seq n)
  let σ_seq : ∀ n, C n → A := fun n => next_σ n (k_seq n)
  let τ_seq : ∀ n, (ℕ → ℕ) → ℕ → ℕ := fun n => next_τ n (k_seq n)

  -- We define the sequence of separating sets `An` for the lemma.
  -- Conceptually, this will be constructed from your cylinder bounds (e.g., cyl (k_seq n))
  -- or closely bound the range of σ_seq to satisfy the disjointness and open-image requirements.
  let An : ℕ → Set A := fun n => sorry

  -- Apply the lemma to conclude the main goal
  apply pointedGluing_lower_bound_lemma' f C D g x An

  · -- hclopen: ∀ n, IsClopen (An n)
    intro n
    sorry

  · -- hsep: ∀ n, f x ∉ closure (f '' (An n))
    -- (Hint: This follows from hdisj in your step_builder, since cylfx m contains f '' cyl l)
    intro n
    sorry

  · -- hpart: ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n))
    -- (Hint: Use the nested property k_{n+1} = l_n to show forward sets fall into cylfx m)
    intro m n hmn
    sorry

  · -- hpart_open: ∀ n, IsOpen (f '' (An n) : Set B)
    intro n
    sorry

  · -- hconv: SetsConvergeTo An x
    -- (Hint: Follows because An n is bounded by cyl (k_seq n), and k_seq is strictly increasing)
    sorry

  · -- hred: ∀ n, ContinuouslyReduces (fun z => g n z) (f ∘ Subtype.val : An n → A)
    -- Provide your extracted functions `σ_seq n` and `τ_seq n` here to build the reduction
    intro n
    sorry

    
/-- **Proposition (Minfunctions). Minimum functions.** -/
theorem minFun_is_minimum'
    (α : Ordinal.{0}) (hα : α < omega1) :
      (∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ)
      (hf : Continuous f),
        ScatteredFun f → (CBLevel f (Order.succ α)).Nonempty →
        ContinuouslyReduces (MinFun α) f) := by
  sorry
