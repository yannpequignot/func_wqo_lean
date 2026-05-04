
import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.CBRankHelpers
import RequestProject.PointedGluing.CBLevelOpenRestrict
import RequestProject.PointedGluing.CBRankSimpleHelpers
import RequestProject.PointedGluing.UpperBoundHelpers
import RequestProject.PointedGluing.ContinuousOnTau
import RequestProject.PointedGluing.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical


set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Section 6: Pointed Gluing as a Lower Bound (Lemma 3.10, Proposition 3.11)
-/


/-- **Lemma (Pgluingaslowerbound).**
Let `f : A → B` be a function between metrizable spaces and `(g_n)_n` a sequence in 𝒞.
If there is a point `x ∈ A` and a sequence `(A_n)_n` of clopen sets satisfying:
1. `f(x) ∉ cl(f(A_n))` for all `n`,
2. The sets `f(A_n)` form a relative clopen partition,
3. `A_n → x` (sets converge to `x`),
4. `g_n ≤ f|_{A_n}` for all `n`,
then `pgl_n g_n ≤ f`.


The proof constructs `σ` mapping `0^ω ↦ x` and `(0)^n(1)x' ↦ σ_n(x')`, and
`τ` mapping `f(x) ↦ 0^ω` and `y ↦ (0)^n(1)τ_n(y)` for `y ∈ f(A_n)`.
Continuity follows from Lemma (prop:sufficientcondforcont). -/
theorem pointedGluing_lower_bound_lemma
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
  /-
  ## Step 1: Extract component reductions from hred
  ContinuouslyReduces (g n) (f ∘ Subtype.val : An n → B) unpacks as:
    ∃ σ_n : C n → An n,   -- maps C n into the clopen piece An n
    ∃ τ_n : B → ℕ → ℕ,   -- maps B back to ℕ → ℕ
      Continuous σ_n ∧
      ContinuousOn τ_n (range ((f ∘ Subtype.val) ∘ σ_n)) ∧
      ∀ z : C n, (g n z : ℕ → ℕ) = τ_n (f (σ_n z).val)
  -/
  -- Repack hred so that choose gives σ_n and τ_n simultaneously
  have hred' : ∀ n, ∃ (sn : C n → An n) (tn : B → ℕ → ℕ),
      Continuous sn ∧
      ContinuousOn tn (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ sn)) ∧
      ∀ z : C n, (g n z : ℕ → ℕ) = tn (f (sn z).val) := by
    intro n
    obtain ⟨sn, hsn, tn, htn, heqn⟩ := hred n
    exact ⟨sn, tn, hsn, htn, heqn⟩
  choose σ_n τ_n hσ_n hτ_n hτ_n_eq using hred'
  -- σ_n : ∀ n, C n → An n
  -- τ_n : ∀ n, B → ℕ → ℕ
  -- hσ_n : ∀ n, Continuous (σ_n n)
  -- hτ_n : ∀ n, ContinuousOn (τ_n n) (range ((f ∘ Subtype.val) ∘ σ_n n))
  -- hτ_n_eq : ∀ n z, (g n z : ℕ → ℕ) = τ_n n (f (σ_n n z).val)

  /-
  ## Step 2: Define σ : PointedGluingSet C → A
  • zeroStream ↦ x
  • prependZerosOne n a ↦ (σ_n n ⟨a, hmem⟩).val   (lands in An n ⊆ A)
  We identify n = firstNonzero z.val and a = stripZerosOne n z.val.
  -/
  let σ : PointedGluingSet C → A := fun z =>
    if h : z.val = zeroStream then x
    else
      -- z is in block n, strip the prefix to get the C n element
      (σ_n (firstNonzero z.val)
        ⟨stripZerosOne (firstNonzero z.val) z.val,
         strip_mem_of_pointedGluingSet C z h⟩).val

  /-
  ## Step 3: Define τ : B → ℕ → ℕ
  • f x ↦ zeroStream  (and any y not in any block range)
  • y ∈ range(f ∘ Subtype.val ∘ σ_n n) ↦ prependZerosOne n (τ_n n y)
  Well-defined: ranges of different blocks are disjoint (from hpart, since σ_n n maps
  into An n and the f '' (An m) are pairwise disjoint), and f x is in none of them
  (since f x ∉ closure(f '' (An n)) ⊇ f '' (An n) ⊇ range(f ∘ σ_n n)).
  -/
  -- Helper: f x is not in range(f ∘ Subtype.val ∘ σ_n n) for any n
  have hfx_not_in_range : ∀ n, f x ∉ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) := by
    intro n ⟨z, hz⟩
    -- f (σ_n n z).val ∈ f '' (An n)
    have hmem : f (σ_n n z).val ∈ f '' (An n) :=
      ⟨(σ_n n z).val, (σ_n n z).property, rfl⟩
    -- But f x ∉ closure (f '' (An n)) ⊇ f '' (An n)
    exact hsep n (hz ▸ subset_closure hmem)
  -- Helper: uniqueness of block index
  -- If y ∈ range(f ∘ σ_n m) ∩ range(f ∘ σ_n n) then m = n
  -- Helper: ranges of different blocks are disjoint
  -- (σ_n k maps into An k, and f '' (An m) ∩ f '' (An n) = ∅ for m ≠ n by hpart)
  have hrange_disj : ∀ i j, i ≠ j →
      Disjoint (Set.range ((f ∘ (Subtype.val : An i → A)) ∘ σ_n i))
               (Set.range ((f ∘ (Subtype.val : An j → A)) ∘ σ_n j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro y ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩
    -- y ∈ f '' (An i) and y ∈ f '' (An j), contradicting hpart i j hij
    have hy_i : y ∈ f '' (An i) := ⟨(σ_n i z₁).val, (σ_n i z₁).property, hz₁⟩
    have hy_j : y ∈ f '' (An j) := ⟨(σ_n j z₂).val, (σ_n j z₂).property, hz₂⟩
    exact (Set.disjoint_left.mp (hpart i j hij) hy_i hy_j).elim
  let τ : B → ℕ → ℕ := fun y =>
    if h : ∃ n, y ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) then
      -- The block index is unique by hrange_disj; Classical.choose picks one
      prependZerosOne (Classical.choose h) (τ_n (Classical.choose h) y)
    else
      zeroStream  -- includes y = f x

  /-
  ## Step 4: Prove the reduction
  -/
  refine ⟨σ, ?_, τ, ?_, ?_⟩

  -- ── Goal A: Continuous σ ──────────────────────────────────────────────────
  · /-
    Use sufficient_cond_continuity with U = {z : PointedGluingSet C | z.val ≠ zeroStream}.
    • U is open (complement of the singleton {zeroStream}).
    • On U: σ is continuous by the local block structure (each block maps via σ_n n
        composed with the strip/subtype coercions, all continuous).
    • On Uᶜ = {⟨zeroStream, _⟩}: σ is constant (= x).
    • Sequential condition: z_k ∈ U, z_k → ⟨zeroStream, _⟩.
        Then firstNonzero(z_k) → ∞ (by firstNonzero_tendsto_of_converge_zeroStream).
        σ(z_k) ∈ An_{firstNonzero(z_k)}, and An_n → x by hconv, so σ(z_k) → x.
    -/
    apply sufficient_cond_continuity σ {z : PointedGluingSet C | z.val ≠ zeroStream}
    · -- U is open: singleton {zeroStream} is closed in ℕ → ℕ (discrete-like topology),
      --   so the preimage under Subtype.val is closed, complement is open.
      have hclosed : IsClosed ({⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩} :
          Set (PointedGluingSet C)) := by
        exact isClosed_singleton
      rw [show {z : PointedGluingSet C | z.val ≠ zeroStream} =
          ({⟨zeroStream, zeroStream_mem_pointedGluingSet C⟩} : Set (PointedGluingSet C))ᶜ
          from by ext z; simp [Subtype.ext_iff]]
      exact hclosed.isOpen_compl
    · -- σ continuous on U:
      --   For z ∈ U, z is in some block n = firstNonzero z.val.
      --   On the open set {z | (∀ k < n, z k = 0) ∧ z n ≠ 0} ∩ PointedGluingSet C,
      --   σ equals Subtype.val ∘ σ_n n ∘ ⟨stripZerosOne n ·, hmem⟩, which is continuous.
      intro z hz
      -- hz : z.val ≠ zeroStream
      simp only [Set.mem_setOf_eq] at hz
      set n := firstNonzero z.val with hn_def
      -- The open block {z' | firstNonzero z'.val = n} contains z
      -- On this block, σ z' = (σ_n n ⟨stripZerosOne n z'.val, _⟩).val
      -- This is continuous as a composition.
      apply ContinuousWithinAt.mono _ (Set.subset_univ _)
      -- Goal: ContinuousWithinAt σ Set.univ z  (= ContinuousAt σ z)
      -- Step 1: z is in block n, i.e. (∀ k < n, z.val k = 0) ∧ z.val n ≠ 0
      have hex : ∃ k, z.val k ≠ 0 := not_forall.mp fun h => hz (funext h)
      have h_find_eq : n = Nat.find hex := by
        rw [hn_def]; unfold firstNonzero; exact dif_pos hex
      have h_block : (∀ k, k < n → z.val k = 0) ∧ z.val n ≠ 0 :=
        ⟨fun k hk => by_contra fun hk' => Nat.find_min hex (h_find_eq ▸ hk) hk',
         h_find_eq.symm ▸ Nat.find_spec hex⟩
      -- Step 2: the block {y | (∀ k < n, y.val k = 0) ∧ y.val n ≠ 0} is open
      have hV_open : IsOpen {y : PointedGluingSet C | (∀ k, k < n → y.val k = 0) ∧ y.val n ≠ 0} :=
        (isOpen_block n).preimage continuous_subtype_val
      -- Step 3: σ is ContinuousOn the block — on it, σ = Subtype.val ∘ σ_n n ∘ ⟨stripZerosOne n ·, _⟩
      have hcont_block : ContinuousOn σ
          {y : PointedGluingSet C | (∀ k, k < n → y.val k = 0) ∧ y.val n ≠ 0} := by
        -- On the block, σ y = (σ_n n ⟨stripZerosOne n y.val.val, strip_mem_of_block C y.val n y.prop⟩).val
        -- This is a continuous composition: Subtype.val ∘ σ_n n ∘ (⟨stripZerosOne n ·, _⟩)
        rw [continuousOn_iff_continuous_restrict]
        refine' Continuous.congr _ _
        -- Provide the explicitly continuous function
        use fun y => (σ_n n ⟨stripZerosOne n y.val.val,
            strip_mem_of_block C y.val n y.prop⟩).val
        · -- This is continuous as a composition
          exact continuous_subtype_val.comp
            ((hσ_n n).comp (Continuous.subtype_mk
              ((continuous_stripZerosOne n).comp
                (continuous_subtype_val.comp continuous_subtype_val))
              (fun y => strip_mem_of_block C y.val n y.prop)))
        · -- It agrees pointwise with the restricted σ:
          -- σ y = (σ_n n ⟨stripZerosOne n y.val.val, _⟩).val on the block
          intro y
          have h_eq : firstNonzero y.val.val = n :=
            firstNonzero_eq_of_block y.val.val n y.prop
          simp only [Set.restrict, σ,
                     dif_neg (ne_zeroStream_of_block y.val.val n y.prop), h_eq]
      -- Step 4: ContinuousAt σ z (since z is in the open block) → ContinuousWithinAt
      exact (hcont_block.continuousAt (hV_open.mem_nhds h_block)).continuousWithinAt
    · -- σ continuous on Uᶜ = {⟨zeroStream, _⟩}: σ is constant = x
      apply continuousOn_const.congr
      intro z hz
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
      show σ z = x
      simp only [σ, dif_pos hz]
    · -- Sequential condition: z_k ∈ U with z_k → z₀ = ⟨zeroStream, _⟩
      intro z_k z₀ hz_k hz₀ hz_tendsto
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz₀
      -- σ(z₀) = x
      have hσ_z₀ : σ z₀ = x := by simp only [σ, dif_pos hz₀]
      simp only [hσ_z₀]
      -- z_k.val → zeroStream in ℕ → ℕ
      have hz_val_tendsto : Filter.Tendsto (fun k => (z_k k).val)
          Filter.atTop (nhds zeroStream) := by
        have := hz_tendsto
        rw [tendsto_subtype_rng] at this
        convert this using 1
        simp [hz₀]
      -- firstNonzero(z_k k) → ∞ since z_k.val → zeroStream with z_k.val ≠ zeroStream
      have hfn_tendsto : Filter.Tendsto (fun k => firstNonzero (z_k k).val)
          Filter.atTop Filter.atTop :=
        firstNonzero_tendsto_of_converge_zeroStream
          (fun k => hz_k k)  -- z_k.val ≠ zeroStream
          hz_val_tendsto
      -- σ(z_k k) ∈ An (firstNonzero (z_k k).val), and An n → x by hconv
      -- So σ(z_k k) → x because firstNonzero → ∞ and SetsConvergeTo An x
      rw [tendsto_nhds]
      intro U hU hxU
      -- By SetsConvergeTo, there exists m such that ∀ n ≥ m, An n ⊆ U
      obtain ⟨m, hm⟩ := hconv U hU hxU
      -- By hfn_tendsto, eventually firstNonzero (z_k k).val ≥ m
      filter_upwards [hfn_tendsto (Filter.eventually_ge_atTop m)] with k hk
      -- σ(z_k k) ∈ An (firstNonzero (z_k k).val) ⊆ U
      have hσ_mem : σ (z_k k) ∈ An (firstNonzero (z_k k).val) := by
        simp only [σ, dif_neg (hz_k k)]
        exact (σ_n (firstNonzero (z_k k).val)
          ⟨stripZerosOne (firstNonzero (z_k k).val) (z_k k).val,
           strip_mem_of_pointedGluingSet C (z_k k) (hz_k k)⟩).property
      exact hm (firstNonzero (z_k k).val) hk hσ_mem

  -- ── Goal B: ContinuousOn τ (range (f ∘ σ)) ───────────────────────────────
  · /-
    range (f ∘ σ) = {f x} ∪ ⋃_n range(f ∘ Subtype.val ∘ σ_n n).
    We show ContinuousWithinAt τ (range (f ∘ σ)) at each point.

    Case y = f x: τ(f x) = zeroStream. For sequences y_k → f x in range(f ∘ σ)\{f x},
      the block indices n_k → ∞ (otherwise a subsequence lives in some range(f ∘ σ_n m),
      and f x ∈ closure(f '' (An m)), contradicting hsep m).
      Then τ(y_k) = prependZerosOne n_k (τ_n n_k y_k) → zeroStream.

    Case y ≠ f x: y ∈ range(f ∘ Subtype.val ∘ σ_n n) for unique n.
      On this block, τ = prependZerosOne n ∘ τ_n n (locally).
      Continuity from τ_n n's ContinuousOn hypothesis.
    -/
    -- First establish that τ on the range sends f x to zeroStream
    have hτ_at_fx : τ (f x) = zeroStream := by
      -- f x is not in range(f ∘ σ_n n) for any n, so the dif is false
      have h_not : ¬ ∃ n, f x ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) :=
        fun ⟨n, hn⟩ => hfx_not_in_range n hn
      simp only [τ, dif_neg h_not]
    -- Show ContinuousOn via ContinuousWithinAt at each point of range (f ∘ σ)
    -- Proof strategy: use sufficient_cond_continuity on τ : B → ℕ → ℕ restricted to
    -- the range. We prove each ContinuousWithinAt τ (range (f ∘ σ)) y separately.
    intro y hy
    obtain ⟨z, rfl⟩ := hy  -- y = f (σ z)
    by_cases hz : z.val = zeroStream
    · /-
      Case y = f(σ(zeroStream)) = f x.
      τ(f x) = zeroStream.
      We show ContinuousWithinAt τ (range (f ∘ σ)) (f x) as follows:
      Take a net/sequence y_k = f(σ(z_k)) → f x in range(f ∘ σ) with y_k ≠ f x.
      Then z_k.val ≠ zeroStream (otherwise y_k = f x), so block indices
        n_k := firstNonzero(z_k.val) are well-defined.
      We need n_k → ∞: otherwise a subsequence lives in {y ∈ range | block n₀},
        giving f x ∈ closure(f '' (An n₀)), contradicting hsep n₀.
      Then τ(y_k) = prependZerosOne n_k (τ_n n_k y_k) → zeroStream = τ(f x).
      (because n_k → ∞ and prependZerosOne k · → zeroStream as k → ∞, by
       prependZerosOne_tendsto_zeroStream)
      -/
      have hσ_z : σ z = x := by simp only [σ, dif_pos hz]
      -- Goal: ContinuousWithinAt τ (range (f ∘ σ)) (f (σ z)) where f (σ z) = f x.
      -- τ(f x) = zeroStream. We prove ContinuousWithinAt by showing τ converges to zeroStream.
      -- Change the point from f(σ z) = f x in the goal
      have hfσ_eq : f (σ z) = f x := by rw [hσ_z]
      rw [show (f ∘ σ) z = f x from hfσ_eq]
      -- Strategy: for each coordinate k, find U ∋ f x open such that
      -- ∀ y ∈ range(f ∘ σ) ∩ U, τ y k = 0.
      -- Key: τ(y) k = 0 for:
      --   y = f x: τ(f x) = zeroStream, ok.
      --   y ∈ range(f ∘ σ_n n) with n > k: τ(y) k = (prependZerosOne n ...) k = 0 (since k < n).
      -- Take U = ⋂_{n ≤ k} (closure(f '' An n))ᶜ (open, contains f x by hsep).
      -- Then range(f ∘ σ) ∩ U only hits blocks n > k (since range(f ∘ σ_n n) ⊆ f '' (An n)
      -- and U is disjoint from f '' (An n) for n ≤ k).
      rw [ContinuousWithinAt, tendsto_pi_nhds]
      intro k
      -- Build U ∋ f x disjoint from f '' (An n) for all n ≤ k
      -- (this is a finite intersection of open sets, each open since closure is closed)
      set U := ⋂ n ∈ Finset.range (k + 1), (closure (f '' (An n)))ᶜ with hU_def
      have hU_open : IsOpen U :=
        isOpen_biInter_finset (fun n _ => isClosed_closure.isOpen_compl)
      have hfx_U : f x ∈ U := by
        simp only [hU_def, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
        exact fun n _ => hsep n
      have hU_disj : ∀ n, n ≤ k → Disjoint U (f '' (An n)) := by
        intro n hn y
        simp only [hU_def, Set.mem_iInter, Finset.mem_range, Set.mem_compl_iff]
        exact fun hy_U hy_An => hy_U n (Nat.lt_succ_of_le hn) (subset_closure hy_An)
      -- Now prove ∀ᶠ y in nhdsWithin (f x) (range(f ∘ σ)), τ y k = zeroStream k
      apply Filter.Tendsto.congr' (tendsto_const_nhds (b := (0 : ℕ)))
      rw [Filter.EventuallyEq, Filter.eventually_nhdsWithin_iff]
      apply Filter.mem_of_superset (hU_open.mem_nhds hfx_U)
      intro y hy_U hy_range
      -- y ∈ range(f ∘ σ) ∩ U: show τ y k = zeroStream k = 0
      simp only [zeroStream]
      -- y = f(σ w) for some w
      obtain ⟨w, rfl⟩ := hy_range
      by_cases hw : w.val = zeroStream
      · -- y = f x: τ(y) = zeroStream
        simp only [σ, dif_pos hw]
        rw [hτ_at_fx]
        simp [zeroStream]
      · -- y ∈ range(f ∘ σ_n n) for n = firstNonzero w.val
        set n_w := firstNonzero w.val
        -- n_w > k because y = f(σ w) ∈ f '' (An n_w) and U is disjoint from f '' (An n_w) for n_w ≤ k
        have hσ_w : σ w = (σ_n n_w ⟨stripZerosOne n_w w.val,
            strip_mem_of_pointedGluingSet C w hw⟩).val := by
          simp only [σ, dif_neg hw]
        have hy_An : f (σ w) ∈ f '' (An n_w) := by
          rw [hσ_w]
          exact ⟨(σ_n n_w ⟨stripZerosOne n_w w.val, strip_mem_of_pointedGluingSet C w hw⟩).val,
                 (σ_n n_w ⟨stripZerosOne n_w w.val, strip_mem_of_pointedGluingSet C w hw⟩).property,
                 rfl⟩
        have hn_w_gt_k : n_w > k := by
          by_contra hle
          push_neg at hle
          exact Set.disjoint_left.mp (hU_disj n_w hle) hy_U hy_An
        -- τ(f(σ w)) = prependZerosOne n_w (τ_n n_w (f(σ w)))
        have hfw_range : f (σ w) ∈ Set.range ((f ∘ (Subtype.val : An n_w → A)) ∘ σ_n n_w) :=
          ⟨⟨stripZerosOne n_w w.val, strip_mem_of_pointedGluingSet C w hw⟩,
           by simp only [Function.comp, hσ_w]⟩
        have hτ_w : τ (f (σ w)) = prependZerosOne n_w (τ_n n_w (f (σ w))) := by
          simp only [τ, dif_pos ⟨n_w, hfw_range⟩]
          set m_w := Classical.choose (⟨n_w, hfw_range⟩ : ∃ k,
              f (σ w) ∈ Set.range ((f ∘ (Subtype.val : An k → A)) ∘ σ_n k))
          have hm_range : f (σ w) ∈ Set.range ((f ∘ (Subtype.val : An m_w → A)) ∘ σ_n m_w) :=
            Classical.choose_spec _
          have hm_eq : m_w = n_w := by
            by_contra hne
            exact absurd hfw_range (Set.disjoint_left.mp (hrange_disj m_w n_w hne) hm_range)
          rw [hm_eq]
        -- τ(f(σ w)) k = prependZerosOne n_w ... k = 0 since k < n_w
        rw [hτ_w]
        simp only [prependZerosOne, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hn_w_gt_k]
        simp [hn_w_gt_k]
    · /-
      Case y = f(σ z) with z.val ≠ zeroStream: z is in block n₀ = firstNonzero(z.val).
      Then y ∈ range(f ∘ Subtype.val ∘ σ_n n₀).
      Locally (on range(f ∘ σ) ∩ neighborhood of y), τ = prependZerosOne n₀ ∘ τ_n n₀.
      ContinuousOn τ_n n₀ on range((f ∘ Subtype.val) ∘ σ_n n₀) gives ContinuousWithinAt
      at y; composing with the continuous prependZerosOne n₀ gives the result.
      -/
      set n := firstNonzero z.val
      have hσ_z : σ z = (σ_n n ⟨stripZerosOne n z.val,
          strip_mem_of_pointedGluingSet C z hz⟩).val := by
        -- Directly unfold σ: since z.val ≠ zeroStream, σ z = (σ_n n ⟨stripZerosOne n z.val, _⟩).val
        -- n := firstNonzero z.val, so after unfolding σ the result is definitionally equal
        simp only [σ, dif_neg hz]
      -- f(σ z) ∈ range(f ∘ Subtype.val ∘ σ_n n)
      have hy_range : f (σ z) ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) :=
        ⟨⟨stripZerosOne n z.val, strip_mem_of_pointedGluingSet C z hz⟩,
         by simp only [Function.comp, hσ_z]⟩
      -- f(σ z) ∈ f '' (An n) (open by hpart_open n)
      have hy_fAn : f (σ z) ∈ f '' (An n) := by
        rw [hσ_z]
        exact ⟨(σ_n n ⟨stripZerosOne n z.val, strip_mem_of_pointedGluingSet C z hz⟩).val,
               (σ_n n ⟨stripZerosOne n z.val, strip_mem_of_pointedGluingSet C z hz⟩).property,
               rfl⟩
      -- Key: range(f ∘ σ) ∩ f '' (An n) = range(f ∘ σ_n n)
      -- (since elements from other blocks land in disjoint sets, and f x ∉ f '' An n by hsep)
      have hrange_eq : Set.range (f ∘ σ) ∩ f '' (An n) = Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_range, Function.comp]
        constructor
        · rintro ⟨⟨w, rfl⟩, hy_An⟩
          by_cases hw : w.val = zeroStream
          · -- y = f x, but f x ∉ f '' (An n) by hsep
            simp only [σ, dif_pos hw] at hy_An
            exact absurd (subset_closure hy_An) (hsep n)
          · -- y = f(σ_n m ⟨...⟩) for m = firstNonzero w.val
            set m := firstNonzero w.val
            have hσ_w : σ w = (σ_n m ⟨stripZerosOne m w.val,
                strip_mem_of_pointedGluingSet C w hw⟩).val := by
              simp only [σ, dif_neg hw]
              -- m := firstNonzero w.val, so this is definitionally equal
              rfl
            have hy_Am : f (σ w) ∈ f '' (An m) :=
              ⟨(σ_n m ⟨stripZerosOne m w.val, strip_mem_of_pointedGluingSet C w hw⟩).val,
               (σ_n m ⟨stripZerosOne m w.val, strip_mem_of_pointedGluingSet C w hw⟩).property,
               by rw [hσ_w]⟩
            have hm_eq_n : m = n := by
              by_contra hne
              exact Set.disjoint_left.mp (hpart m n hne) hy_Am hy_An
            -- m = n, so y ∈ range(f ∘ σ_n n)
            -- strip_mem_of_pointedGluingSet gives stripZerosOne (firstNonzero w.val) w.val ∈ C (firstNonzero w.val)
            -- = stripZerosOne m w.val ∈ C m, and m = n, so stripZerosOne n w.val ∈ C n
            have hstrip : stripZerosOne n w.val ∈ C n := hm_eq_n ▸ strip_mem_of_pointedGluingSet C w hw
            refine ⟨⟨stripZerosOne n w.val, hstrip⟩, ?_⟩
            -- Need: ((f ∘ Subtype.val) ∘ σ_n n) ⟨stripZerosOne n w.val, hstrip⟩ = f (σ w)
            -- σ w = (σ_n m ⟨...⟩).val and m = n, cast via hm_eq_n
            have hσ_cast : σ w = (σ_n n ⟨stripZerosOne n w.val, hstrip⟩).val :=
              hm_eq_n ▸ hσ_w
            simp only [Function.comp, hσ_cast]
        · rintro ⟨a, rfl⟩
          -- y = f ((σ_n n a).val) ∈ range(f ∘ σ) ∩ f '' (An n)
          constructor
          · -- Show f((σ_n n a).val) ∈ range(f ∘ σ)
            -- Use the witness w = ⟨prependZerosOne n a.val, _⟩ : PointedGluingSet C
            have hw_mem : prependZerosOne n a.val ∈ PointedGluingSet C :=
              prependZerosOne_mem_pointedGluingSet C n a.val a.property
            refine ⟨⟨prependZerosOne n a.val, hw_mem⟩, ?_⟩
            -- σ ⟨prependZerosOne n a.val, _⟩ = (σ_n n ⟨stripZerosOne n (prependZerosOne n a.val), _⟩).val
            -- = (σ_n n ⟨a.val, _⟩).val = (σ_n n a).val
            simp only [Function.comp, σ,
                       dif_neg (prependZerosOne_ne_zeroStream n a.val),
                       firstNonzero_prependZerosOne,
                       stripZerosOne_prependZerosOne]
          · -- Show f((σ_n n a).val) ∈ f '' (An n)
            exact ⟨(σ_n n a).val, (σ_n n a).property, rfl⟩
      -- Use hpart_open n: f '' (An n) is open in B
      -- range(f ∘ σ) ∩ f '' (An n) is open in range(f ∘ σ)
      -- τ on range(f ∘ σ_n n) = prependZerosOne n ∘ τ_n n (from τ definition)
      -- τ_n n is ContinuousOn range(f ∘ σ_n n) = range(f ∘ σ) ∩ f '' (An n)
      -- Use ContinuousWithinAt.mono: ContinuousWithinAt τ (range f∘σ ∩ f''(An n)) y
      --   → ContinuousWithinAt τ (range f∘σ) y (since f''(An n) is open, it's a nbhd)
      -- Plan: work with prependZerosOne n ∘ τ_n n, show it's ContinuousWithinAt on range f∘σ
      -- Step 1: ContinuousOn (prependZerosOne n ∘ τ_n n) (range(f ∘ σ_n n))
      have h_cont_block : ContinuousOn (fun y' => prependZerosOne n (τ_n n y'))
          (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n)) :=
        (continuous_prependZerosOne n).continuousOn.comp (hτ_n n) (Set.mapsTo_univ _ _)
      -- Step 2: on range(f ∘ σ) ∩ f '' (An n) = range(f ∘ σ_n n), τ = prependZerosOne n ∘ τ_n n
      have hτ_eq_on_block : ∀ y' ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n),
          τ y' = prependZerosOne n (τ_n n y') := by
        intro y' hy'
        simp only [τ, dif_pos ⟨n, hy'⟩]
        set m' := Classical.choose (⟨n, hy'⟩ : ∃ k, y' ∈ Set.range ((f ∘ (Subtype.val : An k → A)) ∘ σ_n k))
        have hm'_range : y' ∈ Set.range ((f ∘ (Subtype.val : An m' → A)) ∘ σ_n m') :=
          Classical.choose_spec _
        have hm'_eq : m' = n := by
          by_contra hne
          exact absurd hy' (Set.disjoint_left.mp (hrange_disj m' n hne) hm'_range)
        rw [hm'_eq]
      -- Step 3: use ContinuousWithinAt via the open neighborhood f '' (An n)
      -- τ = prependZerosOne n ∘ τ_n n on range(f ∘ σ) ∩ f '' (An n)
      -- and this set equals range(f ∘ σ_n n) which has ContinuousOn
      -- ContinuousWithinAt τ (range f∘σ ∩ f''(An n)) (f(σ z))
      -- Step 3: τ is ContinuousWithinAt (range(f ∘ σ_n n)) at f(σ z), via congr with h_cont_block
      have h_cwat_block : ContinuousWithinAt τ
          (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n)) (f (σ z)) :=
        (h_cont_block.continuousWithinAt hy_range).congr
          (fun y hy => (hτ_eq_on_block y hy).symm) (hτ_eq_on_block _ hy_range).symm
      -- Step 4: range(f ∘ σ) ∩ f '' (An n) = range(f ∘ σ_n n), so τ is cont within the intersection
      have h_cwat_inner : ContinuousWithinAt τ
          (Set.range (f ∘ σ) ∩ f '' (An n)) (f (σ z)) := by
        rw [hrange_eq]; exact h_cwat_block
      -- Step 5: since f '' (An n) is open and f(σ z) ∈ f '' (An n),
      -- nhdsWithin (f(σ z)) (range f∘σ ∩ f''(An n)) = nhdsWithin (f(σ z)) (range f∘σ)
      -- by nhdsWithin_inter_of_mem' (f''(An n) ∈ nhdsWithin (range(f ∘ σ)) (f(σ z)))
      have h_mem_nhds : f '' (An n) ∈ 𝓝[Set.range (f ∘ σ)] (f (σ z)) :=
        mem_nhdsWithin_of_mem_nhds (hpart_open n |>.mem_nhds hy_fAn)
      rw [ContinuousWithinAt, ← nhdsWithin_inter_of_mem' h_mem_nhds]
      exact h_cwat_inner

  -- ── Goal C: Equation ∀ z, PointedGluingFun C D g z = τ (f (σ z)) ─────────
  · intro z
    by_cases hz : z.val = zeroStream
    · /-
      z = zeroStream:
        LHS = PointedGluingFun C D g ⟨zeroStream, _⟩ = zeroStream   (by definition)
        RHS = τ (f (σ ⟨zeroStream, _⟩)) = τ (f x) = zeroStream      (by definition of τ)
      -/
      have hLHS : PointedGluingFun C D g z = zeroStream := by
        simp only [PointedGluingFun, dif_pos hz]
      have hσ_z : σ z = x := by simp only [σ, dif_pos hz]
      have hτ_fx : τ (f x) = zeroStream := by
        have h_not : ¬ ∃ n, f x ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) :=
          fun ⟨n, hn⟩ => hfx_not_in_range n hn
        simp only [τ, dif_neg h_not]
      -- The goal may be (fun z => PointedGluingFun C D g z) z = τ (f (σ z)) due to beta reduction
      show PointedGluingFun C D g z = τ (f (σ z))
      rw [hLHS, hσ_z, hτ_fx]
    · /-
      z ≠ zeroStream: z is in block n = firstNonzero z.val.
        LHS = PointedGluingFun C D g z
            = prependZerosOne n (g n a).val          (by pointedGluingFun_eq_on_block)
        σ(z) = (σ_n n a).val ∈ An n
        f(σ z) ∈ range(f ∘ Subtype.val ∘ σ_n n)
        τ(f(σ z)) = prependZerosOne n (τ_n n (f(σ z)))  (by definition of τ, unique block n)
        hτ_n_eq n a : (g n a : ℕ → ℕ) = τ_n n (f (σ_n n a).val)
        So LHS = prependZerosOne n (τ_n n (f(σ_n n a).val)) = RHS.
      -/
      set n := firstNonzero z.val with hn_def
      set a : C n := ⟨stripZerosOne n z.val, strip_mem_of_pointedGluingSet C z hz⟩
      -- LHS
      have hLHS : PointedGluingFun C D g z = prependZerosOne n (g n a).val :=
        pointedGluingFun_eq_on_block C D g z hz
      -- σ z = (σ_n n a).val since n = firstNonzero z.val and a = ⟨stripZerosOne n z.val, _⟩
      have hσ_z : σ z = (σ_n n a).val := by simp only [σ, dif_neg hz]
      -- f(σ z) is in the range of block n
      have hfσ_range : f (σ z) ∈ Set.range ((f ∘ (Subtype.val : An n → A)) ∘ σ_n n) :=
        ⟨a, by simp only [Function.comp, hσ_z]⟩
      -- τ selects block n (unique by hrange_disj)
      have hτ_eq : τ (f (σ z)) = prependZerosOne n (τ_n n (f (σ z))) := by
        simp only [τ, dif_pos ⟨n, hfσ_range⟩]
        -- Let m = Classical.choose ⟨n, hfσ_range⟩, show m = n by disjointness
        set m := Classical.choose (⟨n, hfσ_range⟩ : ∃ k,
            f (σ z) ∈ Set.range ((f ∘ (Subtype.val : An k → A)) ∘ σ_n k)) with hm_def
        have hm_range : f (σ z) ∈ Set.range ((f ∘ (Subtype.val : An m → A)) ∘ σ_n m) :=
          Classical.choose_spec _
        have hmn : m = n := by
          by_contra hne
          exact absurd hfσ_range
            (Set.disjoint_left.mp (hrange_disj m n hne) hm_range)
        rw [hmn]  -- rewrite m → n so both sides are identical
      -- Rewrite: LHS = prependZerosOne n (g n a), RHS = prependZerosOne n (τ_n n (f (σ z)))
      -- Note: apply hτ_eq before hσ_z since hτ_eq refers to τ (f (σ z))
      rw [hLHS, hτ_eq]
      congr 1
      -- Goal: (g n a : ℕ → ℕ) = τ_n n (f (σ z))
      -- Rewrite σ z = (σ_n n a).val to match hτ_n_eq
      rw [hσ_z]
      -- Goal: (g n a : ℕ → ℕ) = τ_n n (f (σ_n n a).val)
      exact hτ_n_eq n a


/-- **Proposition (Pgluingaslowerbound2). Pointed gluing as lower bound.**
Let `f : A → B` be continuous in 𝒞 and `(g_i)_i` a sequence in 𝒞.
If for all `i ∈ ℕ` and all open neighborhoods `U ∋ x`, there is a continuous
reduction `(σ, τ)` from `g_i` to `f` with `im(σ) ⊆ U` and
`f(x) ∉ cl(im(f ∘ σ))`, then `pgl_i g_i ≤ f`.


In fact, `pgl_i g_i ≤ f|_V` for all clopen neighborhoods `V` of `x`.


The proof constructs a sequence `(A_n)_n` of clopen sets by induction, choosing
each `A_n` so that `f(A_n)` is separated from the previous ones and from `f(x)`,
and `A_n ⊆ N_{x|_n}`. Then applies Lemma (Pgluingaslowerbound). -/
theorem pointedGluing_lower_bound
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
        (∀ z, σ z ∈ U) ∧
        f x ∉ closure (Set.range (fun z => f (σ z)))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  sorry


/-- **Proposition (Minfunctions). Minimum functions.**
For all `α < ω₁`, there exists a function `k_{α+1}` that is minimum in `𝒞_{≥α+1}`:
for all `f ∈ 𝒞` with `CB(f) ≥ α + 1`, we have `k_{α+1} ≤ f`.


The proof is by strong induction on `α`:
- For `α = 0`, `k_1 ≡ id_1` reduces to any nonempty function.
- For successor `α = β + 1`, use Pgluingaslowerbound2: find a ray of CB-rank `α`
  in any neighborhood of a CB_α-point, and apply the induction hypothesis.
- For limit `α`, similarly find rays of growing CB-rank using regularity. -/
theorem minFun_is_minimum
    (α : Ordinal.{0}) (hα : α < omega1) :
      -- minfun α is minimum: for all f with CB(f) ≥ α + 1, minf ≤ f
      (∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ)
      (hf : Continuous f),
        ScatteredFun f → (CBLevel f (Order.succ α)).Nonempty →
        ContinuouslyReduces (MinFun α) f) := by
  sorry
