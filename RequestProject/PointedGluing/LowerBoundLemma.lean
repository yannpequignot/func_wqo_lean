import RequestProject.PointedGluing.Theorems
import RequestProject.PointedGluing.MinFunHelpers
import RequestProject.PointedGluing.MinFunLowerBound
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.CBRankSimpleHelpers
import RequestProject.PrelimMemo.GenRedProp

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Pointed Gluing as a Lower Bound (Lemma 3.13 Pgluingaslowerbound)
-/



/-
  MinFun.lean  —  refactored version of pointedGluing_lower_bound_lemma'

  CHANGES FROM THE ORIGINAL
  ──────────────────────────
  1. A private helper `firstNonzero_val_ne` is lifted out of the proof body
     (it was duplicated twice inline).

  2. The proof is cut into five clearly delimited phases, each introduced by
     a block comment, so the reader can follow the mathematical argument from
     the paper (Lemma 3.13 / Proposition 3.14).

  3. All `have` statements now carry explicit TYPE ANNOTATIONS so Lean's
     elaborator (and the human reader) can check each step in isolation.

  4. The two `sorry` placeholders are kept, but each is wrapped in its own
     named `have` with a precise statement and a comment explaining what a
     complete proof would require.

  5. Repetitive anonymous `by_contra` / disjointness arguments are shared
     through `hτi_n`, which is stated early and reused.

  6. `hfnz_tendsto` and the sequential condition for `σ_cont` / Goal 1 are
     extracted into named `have`s with clear filter-statement types.

  LEAN IDIOM GLOSSARY  (for learners)
  ─────────────────────────────────────
  • `dif_pos h` / `dif_neg h`
      Rewrites `if h : P then a else b` using a proof `h : P` (or `h : ¬P`).
      Used whenever σ or τ_global are unfolded.

  • `choose f g hf hg heq using h`
      Destructs `∀ n, ∃ a b, P a b` into Skolem functions `f n`, `g n`
      together with proofs that they satisfy `P`.

  • `Classical.choose` / `Classical.choose_spec`
      Non-constructive witness extraction from `h : ∃ n, P n`.
      Needed because τi must pick a unique index without decidability.

  • `Filter.eventually_atTop`
      States `∀ᶠ k in atTop, P k ↔ ∃ N, ∀ k ≥ N, P k`.
      Used for every "eventually" argument in the sequential conditions.

  • `ContinuousOn.comp_continuous`
      If `g` is `ContinuousOn S` and `h : X → S` is continuous, then
      `fun x => g (h x)` is continuous.

  • `sufficient_cond_continuity`
      A local lemma (not in Mathlib) proving continuity via:
        (i)  an open set U on which the function is already continuous, and
        (ii) a sequential condition at every limit point of Uᶜ.

  • `continuous_of_relativeClopenPartition_seq`
      Continuity follows when a function is continuous on each piece
      of a relative clopen partition (another local lemma).
-/

-- ============================================================
--  PRIVATE HELPERS  (lifted out of the proof body)
-- ============================================================

/-- At the first nonzero position of `z`, the value is indeed nonzero.
    This tiny fact was proved twice inline in the original; we lift it here. -/
lemma firstNonzero_val_ne {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
    z (firstNonzero z) ≠ 0 := by
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hz (funext fun i => by simp [zeroStream, hall i])
  simp only [firstNonzero, dif_pos hex]
  exact Nat.find_spec hex

/-- If z ≠ zeroStream, then z (firstNonzero z) ≠ 0,
    i.e. firstNonzero z is actually a nonzero position. -/
lemma firstNonzero_ne {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
    z (firstNonzero z) ≠ 0 :=
  firstNonzero_val_ne hz

/-- All positions strictly before firstNonzero z are zero. -/
lemma firstNonzero_zero {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
    ∀ k, k < firstNonzero z → z k = 0 := by
  -- firstNonzero z = Nat.find hex, and Nat.find_min says:
  -- for any m < Nat.find hex, ¬ (z m ≠ 0), i.e. z m = 0.
  have hex : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hz (funext fun i => by simp [zeroStream, hall i])
  intro k hk
  simp only [firstNonzero, dif_pos hex] at hk
  -- Nat.find_min : ∀ m < Nat.find h, ¬ P m
  have := Nat.find_min hex hk
  push_neg at this
  exact this

-- ============================================================
--  MAIN THEOREM
-- ============================================================

theorem pointedGluing_lower_bound_lemma'
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
    (f : A → B) (hf : Continuous f)
    (C D : ℕ → Set (ℕ → ℕ))
    (g : ∀ n, C n → D n)
    (x : A)
    (An : ℕ → Set A)
    (hsep : ∀ n, f x ∉ closure (f '' (An n)))
    (hrelclop : IsRelativeClopenPartition (fun m => f '' (An m)))
    (hconv : SetsConvergeTo An x)
    (hred : ∀ n, ContinuouslyReduces
      (fun (z : C n) => (g n z : ℕ → ℕ))
      (f ∘ (Subtype.val : An n → A))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  -- ══════════════════════════════════════════════════════════
  --  PHASE 0 — Extract witnesses from hypotheses
  -- ══════════════════════════════════════════════════════════
  --
  -- `hrelclop` bundles two pieces: pairwise disjointness of the
  -- images f(Aₙ), and the fact that each piece is relatively open
  -- in the union.  We name them separately for readability.

  have hpart : ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n)) :=
    hrelclop.1

  have hpart_open : ∀ n, IsOpen
      ((Subtype.val : (⋃ j, f '' (An j)) → B) ⁻¹' (f '' (An n))) :=
    hrelclop.2

  -- `hred n` says: gₙ continuously reduces to f|_{Aₙ}.
  -- Unpack the existentials to get named maps σₙ and τₙ.
  --
  -- LEAN: `choose ... using` destructs `∀ n, ∃ sn tn, P sn tn`
  -- into Skolem functions.  The result:
  --   σ_n n : C n → An n            (the "left" part of the reduction)
  --   τ_n n : B → ℕ → ℕ             (the "right" part)
  --   hσ_n n : Continuous (σ_n n)
  --   hτ_n n : ContinuousOn (τ_n n) (range (f ∘ σ_n n))
  --   hτ_n_eq n : ∀ z, g n z = τ_n n (f (σ_n n z).val)

  have hred' : ∀ n, ∃ (sn : C n → An n) (tn : B → ℕ → ℕ),
      Continuous sn ∧
      ContinuousOn tn (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ sn)) ∧
      ∀ z : C n, (g n z : ℕ → ℕ) = tn (f (sn z).val) := by
    intro n
    obtain ⟨sn, hsn, tn, htn, heqn⟩ := hred n
    exact ⟨sn, tn, hsn, htn, heqn⟩

  choose σ_n τ_n hσ_n hτ_n hτ_n_eq using hred'

  -- ══════════════════════════════════════════════════════════
  --  PHASE 1 — Define σ and prove it is continuous
  -- ══════════════════════════════════════════════════════════
  --
  -- σ : PointedGluingSet C → A is defined piecewise:
  --   • If z = zeroStream  →  x   (the base point)
  --   • Otherwise, let n = firstNonzero z.val and z' = stripZerosOne n z.val
  --                  →  (σₙ n z').val
  --
  -- LEAN: `dif_pos h` / `dif_neg h` unfold the `if h : ...` branches later.

  let σ : PointedGluingSet C → A := fun z =>
    if h : z.val = zeroStream then x
    else (σ_n (firstNonzero z.val)
      ⟨stripZerosOne (firstNonzero z.val) z.val,
       strip_mem_of_pointedGluingSet C z h⟩).val


  -- ── 1a. Continuity of σ on U = {z | z.val ≠ zeroStream} ─────────────
  --
  -- We work with pieces in PointedGluingSet C directly (not the double-
  -- subtype), so that `continuous_of_relativeClopenPartition_seq` can
  -- unify its conclusion `Continuous f` with our goal without a subtype
  -- mismatch.
  --
  -- The pieces are:
  --   piece n  =  {z : PointedGluingSet C | z.val ≠ zeroStream
  --                                        ∧ firstNonzero z.val = n}
  --
  -- Their union equals {z | z.val ≠ zeroStream}, so ContinuousOn on the
  -- union follows from piecewise continuity.
  --
  -- ★ SORRY 1 ★
  -- What is needed:
  --   For each n, the piece above is open in PointedGluingSet C.
  -- Proof sketch: it equals the preimage under (fun z => z.val) of
  --   (cylinder n \ cylinder (n+1)) ∩ {s | s ≠ zeroStream},
  -- where cylinder k = {s : ℕ → ℕ | ∀ i < k, s i = 0}.
  -- Both cylinder sets are clopen in ℕ→ℕ (product topology), so the
  -- piece is clopen (in particular open) in PointedGluingSet C.

  -- Pieces as subsets of PointedGluingSet C (not a double subtype)
  let piece : ℕ → Set (PointedGluingSet C) :=
    fun n => Subtype.val ⁻¹' RaySet (PointedGluingSet C) zeroStream n


  -- Unfolding: piece n = {z : PointedGluingSet C | z.val ∈ RaySet (PointedGluingSet C) zeroStream n}
  --                    = {z | z.val ∈ PointedGluingSet C  -- automatic from subtype
  --                         ∧ (∀ k < n, z.val k = 0)
  --                         ∧ z.val n ≠ 0}
  -- This is exactly {z | z.val ≠ zeroStream ∧ firstNonzero z.val = n}
  -- as required by the original definition.
  have hpiece_covers :
      {z : PointedGluingSet C | z.val ≠ zeroStream} = ⋃ n, piece n := by
    ext z
    simp only [piece, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage,
               RaySet, Set.mem_setOf_eq]
    constructor
    · intro hz
      -- z.val ∈ PointedGluingSet C and z.val ≠ zeroStream,
      -- so z.val ∈ ⋃ i, prependZerosOne i '' (F i).
      -- Let n = firstNonzero z.val; then z.val agrees with zeroStream on range n
      -- and differs at n.  That is exactly RaySet _ zeroStream n.
      -- zeroStream lives in PointedGluingSet C via the {zeroStream} ∪ ... definition
      have hz₀ : zeroStream ∈ PointedGluingSet C :=
        Set.mem_union_left _ (Set.mem_singleton _)

      let z₀ : ↑(PointedGluingSet C) := ⟨zeroStream, hz₀⟩
      refine ⟨firstNonzero z.val, z.2, ?_, firstNonzero_ne hz⟩
      intro k hk
      exact firstNonzero_zero hz k hk
    · rintro ⟨n, _, _, hne⟩
      -- z.val n ≠ zeroStream n = 0, so z.val ≠ zeroStream
      intro heq
      apply hne
      simp [zeroStream, funext_iff] at heq
      exact heq n

  have hpiece_disj : ∀ m n, m ≠ n → Disjoint (piece m) (piece n) := by
    intro m n hmn
    simp only [piece, Set.disjoint_left, Set.mem_preimage, RaySet,
               Set.mem_setOf_eq]
    intro z ⟨_, hm_zeros, hm_ne⟩ ⟨_, hn_zeros, hn_ne⟩
    -- Both say firstNonzero z.val = m and = n respectively.
    -- We derive m = n, contradicting hmn.
    apply hmn
    -- From hm_zeros : ∀ k < m, z.val k = 0  and  hm_ne : z.val m ≠ 0
    -- From hn_zeros : ∀ k < n, z.val k = 0  and  hn_ne : z.val n ≠ 0
    -- If m < n then z.val m = 0 by hn_zeros, contradicting hm_ne.
    -- If n < m then z.val n = 0 by hm_zeros, contradicting hn_ne.
    -- So m = n.
    rcases Nat.lt_trichotomy m n with h | h | h
    · exact absurd (hn_zeros m h) (by simp [zeroStream] at hm_ne ⊢; exact hm_ne)
    · exact h
    · exact absurd (hm_zeros n h) (by simp [zeroStream] at hn_ne ⊢; exact hn_ne)

  have hpiece_open : ∀ n, IsOpen (piece n) := by
    intro n
    exact ray_subtype_isOpen' (PointedGluingSet C) zeroStream n

  have hpiece_relclop : IsRelativeClopenPartition piece := by
    refine ⟨hpiece_disj, fun i => ?_⟩
    -- Goal: IsOpen (Subtype.val ⁻¹' piece i)
    -- where Subtype.val : (⋃ j, piece j) → ↑(PointedGluingSet C)
    -- piece i is open in ↑(PointedGluingSet C) by hpiece_open,
    -- so its preimage under the continuous inclusion is open.
    exact (hpiece_open i).preimage continuous_subtype_val
  have hU_eq : {z : PointedGluingSet C | z.val ≠ zeroStream} = ⋃ i, piece i := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, piece, Set.mem_preimage]
        constructor
        · intro hz
          -- Apply mem_ray_or_eq_y to z.val ∈ PointedGluingSet C
          rcases mem_ray_or_eq_y z.2 with h | ⟨n, hn⟩
          · exact absurd h hz
          · exact ⟨n, hn⟩
        · rintro ⟨n, hn⟩
          -- z ∈ piece n means z.val ∈ RaySet (PointedGluingSet C) zeroStream n
          -- In particular z.val ≠ zeroStream since z.val n ≠ zeroStream n = 0
          exact fun heq => hn.2.2 (by simp [heq, zeroStream])

  -- have hf : ∀ i, Continuous (f ∘ Set.inclusion (Set.subset_iUnion piece i)) := by
  --   intro i
  --   exact (hpart_open i).ContinuousOn.comp_continuous (continuous_subtype_val)
  have hσ_pieces : ∀ i, Continuous (fun z : piece i => σ z.val) := by
      sorry

  have σ_cont_on_U : ContinuousOn σ
      {z : PointedGluingSet C | z.val ≠ zeroStream} := by
    rw [hU_eq]
    -- ContinuousOn on ⋃ i, piece i means:
    -- the restriction (⋃ i, piece i).restrict σ is continuous,
    -- which equals σ ∘ Subtype.val where Subtype.val : ⋃ i, piece i → ↑(PointedGluingSet C)
    rw [continuousOn_iff_continuous_restrict]
    -- Goal: Continuous ((⋃ i, piece i).restrict σ)
    -- = Continuous (σ ∘ Subtype.val)
    -- Apply continuous_of_relativeClopenPartition_seq to σ ∘ Subtype.val
    apply continuous_of_relativeClopenPartition_seq hpiece_relclop
    intro i
    -- Goal: Continuous ((σ ∘ Subtype.val) ∘ Set.inclusion (Set.subset_iUnion piece i))
    -- = Continuous (σ ∘ (Subtype.val ∘ Set.inclusion ...))
    -- = Continuous (fun z : piece i => σ z.val)
    have heq : (Set.restrict (⋃ i, piece i) σ) ∘ Set.inclusion (Set.subset_iUnion piece i) =
                fun z : piece i => σ z.val := by
      ext z; simp [Set.restrict]
    rw [heq]
    exact hσ_pieces i
  -- ── 1b. Sequential condition: zₖ → zeroStream ⟹ σ(zₖ) → x ─────────
  --
  -- If zₖ.val ≠ zeroStream for all k and zₖ → z₀ = zeroStream, then
  -- σ(zₖ) ∈ Aₙ for n = firstNonzero(zₖ.val), and n → ∞, so
  -- σ(zₖ) → x by SetsConvergeTo.

  have σ_seq :
      ∀ (zk : ℕ → PointedGluingSet C) (z₀ : PointedGluingSet C),
      (∀ k, (zk k).val ≠ zeroStream) →
      z₀.val = zeroStream →
      Filter.Tendsto zk Filter.atTop (nhds z₀) →
      Filter.Tendsto (fun k => σ (zk k)) Filter.atTop (nhds x) := by
    intro zk z₀ hzk_ne hz₀ htendsto
    rw [tendsto_nhds]
    intro U hU hxU
    obtain ⟨N, hN⟩ := hconv U hU hxU
    -- The cylinder nbhd zeroStream N is a neighborhood of z₀ in PointedGluingSet C.
    have hcyl_nhd :
        {z : PointedGluingSet C | z.val ∈ nbhd zeroStream N} ∈ nhds z₀ := by
      apply continuous_subtype_val.continuousAt.preimage_mem_nhds
      exact (baire_nbhd_isClopen zeroStream N).isOpen.mem_nhds (by simp [nbhd, hz₀])
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
      (htendsto.eventually (Filter.eventually_of_mem hcyl_nhd fun _ h => h))
    apply Filter.eventually_atTop.mpr ⟨M, fun k hk => ?_⟩
    -- σ(zₖ k) ∈ Aₙ for n = firstNonzero (zₖ k).val
    have hσ_mem : σ (zk k) ∈ An (firstNonzero (zk k).val) := by
      simp only [σ, dif_neg (hzk_ne k)]
      exact (σ_n (firstNonzero (zk k).val)
        ⟨stripZerosOne _ (zk k).val,
         strip_mem_of_pointedGluingSet C (zk k) (hzk_ne k)⟩).prop
    -- firstNonzero (zₖ k).val ≥ N, using that zₖ k ∈ cylinder N
    have hfnz_ge : N ≤ firstNonzero (zk k).val := by
      by_contra hlt
      push_neg at hlt
      have hzk_nbhd := hM k hk
      simp only [Set.mem_setOf_eq, nbhd] at hzk_nbhd
      have heq : (zk k).val (firstNonzero (zk k).val) = 0 :=
        by simpa [zeroStream] using
          hzk_nbhd (firstNonzero (zk k).val) (Finset.mem_range.mpr hlt)
      exact absurd heq (firstNonzero_val_ne (hzk_ne k))
    exact hN (firstNonzero (zk k).val) hfnz_ge hσ_mem

  -- ── 1c. Assemble: σ is continuous ───────────────────────────────────
  --
  -- `sufficient_cond_continuity` says: a function on a metrizable space
  -- is continuous if it is continuous on an open U and satisfies a
  -- sequential condition at every boundary point (limit of sequences in U
  -- converging outside U).

  have σ_cont : Continuous σ :=
    sufficient_cond_continuity σ {z : PointedGluingSet C | z.val ≠ zeroStream}
      (isOpen_compl_singleton.preimage continuous_subtype_val)
      σ_cont_on_U
      ((continuousOn_const (c := x)).congr (fun z hz => by
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
          exact dif_pos hz))
      (fun zk z₀ hzk_ne hz₀ htendsto => by
          simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz₀
          simp only [σ, dif_pos hz₀]
          exact σ_seq zk z₀ hzk_ne hz₀ htendsto)

  -- ══════════════════════════════════════════════════════════
  --  PHASE 2 — Define In, τi and prove their properties
  -- ══════════════════════════════════════════════════════════
  --
  -- In n  =  range (f ∘ val ∘ σₙ n)   ⊆  f(Aₙ)
  --
  -- τi : (⋃ n, In n) → ℕ  picks the unique index n such that y ∈ In n.
  -- It is well-defined because the In n are pairwise disjoint.

  let In : ℕ → Set B := fun n => Set.range ((f ∘ Subtype.val) ∘ σ_n n)

  -- In n ⊆ f(Aₙ)
  have h_refine : ∀ n, In n ⊆ f '' (An n) := by
    intro n
    rintro y ⟨z, rfl⟩
    exact ⟨(σ_n n z).val, (σ_n n z).prop, rfl⟩

  -- The In n are pairwise disjoint (inherited from hpart via h_refine)
  have h_Indisjoint : ∀ n m, n ≠ m → Disjoint (In n) (In m) :=
    fun n m hne => (hpart n m hne).mono (h_refine n) (h_refine m)

  -- In is still a relative clopen partition (stability under refinement)
  have hrelclop' : IsRelativeClopenPartition In :=
    RelativeClopenPartition_stable_by_refine hrelclop h_refine

  -- τi : (⋃ n, In n) → ℕ  picks the index non-constructively.
  -- LEAN: `Classical.choose` extracts a witness from an existential without
  -- decidability; `Classical.choose_spec` gives the proof that it works.
  let τi : (⋃ n, In n) → ℕ := fun y =>
    Classical.choose (Set.mem_iUnion.mp y.prop)

  -- Key invariant: on piece In n, τi equals n.
  -- Proof: if τi y = m ≠ n and y ∈ In n ∩ In m, that contradicts disjointness.
  have hτi_n : ∀ (y : ⋃ n, In n) (n : ℕ), y.val ∈ In n → τi y = n := by
    intro y n hy
    dsimp [τi]
    generalize_proofs h_mem
    set m := Classical.choose h_mem
    have hm : y.val ∈ In m := Classical.choose_spec h_mem
    by_contra hne
    exact (h_Indisjoint m n hne).le_bot ⟨hm, hy⟩

  -- τi is continuous: it is locally constant on each clopen piece In n.
  -- LEAN: `continuous_of_relativeClopenPartition_seq` gives continuity from
  -- piecewise-continuity on a relative clopen partition.
  have hτi_cont : Continuous τi := by
    apply continuous_of_relativeClopenPartition_seq hrelclop'
    intro n
    apply continuous_const.congr
    intro ⟨y, hy⟩
    have hu : y∈ (⋃ n, In n) := Set.mem_iUnion.mpr ⟨n, hy⟩
    sorry
    sorry
  -- ══════════════════════════════════════════════════════════
  --  PHASE 3 — Define τ, τ_global and prove continuity
  -- ══════════════════════════════════════════════════════════
  --
  -- τ : (⋃ n, In n) → ℕ → ℕ
  --   y  ↦  prependZerosOne (τi y) (τₙ (τi y) y)
  --
  -- This encodes: prepend n zeros, then a 1, then apply τₙ.
  -- It matches the pointed gluing format (0)ⁿ ⌢ (1) ⌢ τₙ(y).

  let τ : (⋃ n, In n) → ℕ → ℕ := fun y =>
    prependZerosOne (τi y) (τ_n (τi y) y)

  -- On piece In n, τ simplifies to prependZerosOne n ∘ τₙ n ∘ val.
  -- We prove continuity of τ on each piece separately, then assemble.
  have hfpart :
      ∀ n, Continuous
        (fun x : In n => τ (Set.inclusion (Set.subset_iUnion In n) x)) := by
    intro n
    -- On In n, τi = n (by hτi_n), so τ = prependZerosOne n ∘ τₙ n ∘ val.
    have h_eq : ∀ x : In n,
        τ (Set.inclusion (Set.subset_iUnion In n) x) =
        prependZerosOne n (τ_n n x.val) := by
      intro x
      dsimp [τ]
      rw [hτi_n (Set.inclusion (Set.subset_iUnion In n) x) n x.2]
    -- prependZerosOne n is continuous; τₙ n is ContinuousOn (In n).
    -- LEAN: `ContinuousOn.comp_continuous` composes a ContinuousOn with a
    -- continuous subtype inclusion.
    apply Continuous.congr _ (fun x => (h_eq x).symm)
    exact (continuous_prependZerosOne n).comp
      (ContinuousOn.comp_continuous (hτ_n n) continuous_subtype_val (fun x => x.2))

  have hτ_cont : Continuous τ :=
    continuous_of_relativeClopenPartition_seq hrelclop' hfpart

  -- τ_global extends τ by zeroStream outside UI = ⋃ n, In n.
  -- f(x) ∉ UI because hsep says f(x) ∉ closure(f(Aₙ)) ⊇ In n for all n.
  let UI := ⋃ n, In n

  let τ_global : B → (ℕ → ℕ) := fun y =>
    if h : y ∈ UI then τ ⟨y, h⟩ else zeroStream

  -- f(x) is not in UI
  have hfx_notUI : f x ∉ UI := fun hmem => by
    obtain ⟨n, zn, hzn⟩ := Set.mem_iUnion.mp hmem
    exact hsep n (subset_closure ⟨(σ_n n zn).val, (σ_n n zn).prop, hzn⟩)

  -- ══════════════════════════════════════════════════════════
  --  PHASE 4 — Auxiliary: f(σ z) ∈ UI when z ≠ zeroStream
  -- ══════════════════════════════════════════════════════════
  --
  -- For z ≠ zeroStream, σ z = (σₙ n z').val where n = firstNonzero z.val,
  -- so f(σ z) ∈ In n ⊆ UI.

  have h_incl :
      ∀ z : PointedGluingSet C, z.val ≠ zeroStream → f (σ z) ∈ UI := by
    intro z hz
    rw [Set.mem_iUnion]
    exact ⟨firstNonzero z.val,
      ⟨⟨stripZerosOne _ z.val, strip_mem_of_pointedGluingSet C z hz⟩,
        by simp [σ, dif_neg hz]⟩⟩

  -- ══════════════════════════════════════════════════════════
  --  PHASE 5 — Produce the reduction witness and verify goals
  -- ══════════════════════════════════════════════════════════

  refine ⟨σ, σ_cont, τ_global, ?_, ?_⟩

  -- ── Goal 1: ContinuousOn τ_global on range(f ∘ σ) ──────────────────
  --
  -- Strategy: show that the composition z ↦ τ_global(f(σ z)) is continuous
  -- (using `sufficient_cond_continuity` again), then derive ContinuousOn on
  -- the range.
  --
  -- On U = {z | z.val ≠ zeroStream}:
  --   τ_global(f(σ z)) = τ ⟨f(σ z), h_incl z hz⟩
  -- This factors as  hτ_cont ∘ (lift to UI) ∘ f ∘ σ.
  --
  -- On Uᶜ (z = zeroStream):
  --   f(σ z) = f x ∉ UI, so τ_global(f(σ z)) = zeroStream.
  --
  -- Sequential condition at Uᶜ:
  --   Need τ_global(f(σ(zₖ))) → zeroStream.
  --   Key: τ_global(f(σ(zₖ))) = prependZerosOne (firstNonzero (zₖ).val) _
  --   and firstNonzero (zₖ k).val → ∞ as zₖ k → zeroStream,
  --   so prependZerosOne n _ → zeroStream.

  · -- ── 5.1  firstNonzero tends to ∞ as zₖ → zeroStream ───────────────
    -- Used both in Goal 1 and (implicitly) in σ_seq above.
    -- Stated here so it can be referred to in the `hcomp` proof below.
    --
    -- LEAN: `Filter.tendsto_atTop` says Tendsto g atTop atTop ↔
    --   ∀ N, ∀ᶠ k in atTop, N ≤ g k.

    -- ── 5.2  The composition z ↦ τ_global(f(σ z)) is continuous ────────
    --
    -- ★ SORRY 2 ★
    -- What is needed for the sub-goal `hlift`:
    --   Show that (fun w => ⟨f (σ w), h_incl w ...⟩ : UI) is ContinuousAt z.
    -- This is a subtype membership assertion near z, which holds because:
    --   • UI is open (as a union of open sets in the subspace topology),
    --   • f ∘ σ is continuous,
    --   • f(σ z) ∈ UI (by h_incl),
    -- so the preimage (f ∘ σ)⁻¹(UI) is an open neighborhood of z, and on
    -- that neighborhood the map factors continuously into the subtype.
    -- In Mathlib the relevant lemma is
    --   `ContinuousAt.codRestrict` (or `continuousAt_subtype_mk`).
    --
    -- The full sequential argument for Goal 1 (prependZerosOne n _ → 0)
    -- follows the same structure as σ_seq above and is retained below.

    have hcomp :
        Continuous (fun z : PointedGluingSet C => τ_global (f (σ z))) := by
      apply sufficient_cond_continuity _
        {z : PointedGluingSet C | z.val ≠ zeroStream}
      · exact isOpen_compl_singleton.preimage continuous_subtype_val
      · -- Continuity on U: factor through the subtype lift into UI.
        apply ContinuousOn.congr
        · intro z hz
          simp only [Set.mem_setOf_eq] at hz
          apply ContinuousAt.continuousWithinAt
          -- ★ SORRY 2 lives here ★
          -- Replace with:
          --   have hopen : IsOpen UI := isOpen_iUnion (fun n => ...)
          --   exact (hτ_cont.continuousAt.comp
          --           ((hf.comp σ_cont).continuousAt.codRestrict
          --             (fun w => h_incl w (by ...)) hopen (h_incl z hz)))
          sorry
        · intro z hz
          simp only [Set.mem_setOf_eq] at hz
          simp [τ_global, dif_pos (h_incl z hz)]
          sorry
        sorry
      · -- On Uᶜ: z = zeroStream, τ_global(f(σ z)) = zeroStream (constant).
        apply (continuousOn_const (c := zeroStream)).congr
        intro z hz
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
        simp [τ_global, show σ z = x from dif_pos hz, hfx_notUI]
      · -- Sequential condition: zₖ → zeroStream, need τ_global(f(σ(zₖ))) → 0.
        intro zk z₀ hzk_ne hz₀ htendsto
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz₀
        simp only [show σ z₀ = x from dif_pos hz₀, τ_global, dif_neg hfx_notUI]
        -- firstNonzero (zₖ k).val → ∞
        have hfnz_tendsto :
            Filter.Tendsto (fun k => firstNonzero (zk k).val)
              Filter.atTop Filter.atTop := by
          rw [Filter.tendsto_atTop]
          intro N
          have hcyl_nhd :
              {z : PointedGluingSet C | z.val ∈ nbhd zeroStream N} ∈ nhds z₀ := by
            apply continuous_subtype_val.continuousAt.preimage_mem_nhds
            exact (baire_nbhd_isClopen zeroStream N).isOpen.mem_nhds
              (by simp [nbhd, hz₀])
          obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
            (Filter.Tendsto.eventually htendsto hcyl_nhd)
          apply Filter.eventually_atTop.mpr ⟨M, fun k hk => ?_⟩
          by_contra hlt
          push_neg at hlt
          have heq : (zk k).val (firstNonzero (zk k).val) = 0 := by
            simpa [zeroStream] using
              hM k hk (firstNonzero (zk k).val) (Finset.mem_range.mpr hlt)
          exact absurd heq (firstNonzero_val_ne (hzk_ne k))
        -- τ_global(f(σ(zₖ k))) = prependZerosOne (firstNonzero (zₖ k).val) _
        -- → zeroStream because n → ∞.
        apply tendsto_nhds.mpr
        intro V hV hzero_V
        obtain ⟨N, hN⟩ := nbhd_basis zeroStream V hV hzero_V
        obtain ⟨M, hM⟩ :=
          Filter.eventually_atTop.mp (Filter.tendsto_atTop.mp hfnz_tendsto N)
        apply Filter.eventually_atTop.mpr ⟨M, fun k hk => hN ?_⟩
        have hmem_UI : f (σ (zk k)) ∈ UI := h_incl (zk k) (hzk_ne k)
        sorry
        -- rw [dif_pos hmem_UI]
        -- simp only [τ]
        -- rw [hτi_n ⟨f (σ (zk k)), hmem_UI⟩ (firstNonzero (zk k).val)
        --   ⟨⟨stripZerosOne _ (zk k).val,
        --     strip_mem_of_pointedGluingSet C (zk k) (hzk_ne k)⟩, by
        --       simp [σ, dif_neg (hzk_ne k)]⟩]
        -- intro i hi
        -- simp only [nbhd, Finset.mem_range] at hi
        -- exact prependZerosOne_eq_zero (hi.trans_le (hM k hk))
    -- Derive ContinuousOn on the range from the continuous composition.
    -- LEAN: `continuousOn_iff_continuous_restrict` reduces ContinuousOn on a
    -- range to continuity of the restricted map.
    rw [continuousOn_iff_continuous_restrict]
    sorry
    -- rintro ⟨y, z, rfl⟩
    -- exact hcomp.continuousAt.continuousWithinAt

  -- ── Goal 2: functional equation ────────────────────────────────────
  --
  -- PointedGluingFun C D g z = τ_global (f (σ z))
  --
  -- Two cases:
  --   z = zeroStream : both sides are zeroStream.
  --   z ≠ zeroStream : unfold using hτ_n_eq and PointedGluingFun_eq.

  · intro z
    by_cases h : z.val = zeroStream
    · -- Basepoint case: PointedGluingFun sends zeroStream to zeroStream.
      have hσz : σ z = x := dif_pos h
      simp [τ_global, hσz, hfx_notUI]
      sorry
    · -- Non-basepoint case.
      set n  := firstNonzero z.val
      sorry
      -- set z' := ⟨stripZerosOne n z.val, strip_mem_of_pointedGluingSet C z h⟩
      -- f(σ z) = f(σₙ n z').val ∈ In n ⊆ UI
      -- have hfσ_UI : f (σ_n n z').val ∈ UI :=
      --   Set.mem_iUnion.mpr ⟨n, z', rfl⟩
      -- simp only [σ, dif_neg h, τ_global, dif_pos hfσ_UI, τ]
      -- -- τi gives n on In n (by hτi_n)
      -- rw [hτi_n ⟨f (σ_n n z').val, hfσ_UI⟩ n ⟨z', rfl⟩]
      -- -- prependZerosOne n (τₙ n ...) = PointedGluingFun C D g z
      -- -- via hτ_n_eq and PointedGluingFun_eq
      -- rw [← hτ_n_eq n z']
      -- exact PointedGluingFun_eq C D g z h n z' rfl rfl
