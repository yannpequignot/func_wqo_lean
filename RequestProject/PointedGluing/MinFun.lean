import RequestProject.PointedGluing.Theorems
import RequestProject.PointedGluing.MinFunHelpers
import RequestProject.PointedGluing.MinFunLowerBound
import RequestProject.PointedGluing.Defs
import RequestProject.PrelimMemo.GenRedProp
import RequestProject.PointedGluing.LowerBoundLemma

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
## Section 6: Pointed Gluing as a Lower Bound (Lemma 3.10, Proposition 3.11)
-/

/-
MinFun 0 reduces to any function with nonempty domain.
-/
lemma minFun_zero_reduces {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) -- (hf : Continuous f)
    (hne : A.Nonempty) :
    ContinuouslyReduces (MinFun 0) f := by
  obtain ⟨ x, hx ⟩ := hne;
  refine' ⟨ fun _ => ⟨x, hx⟩, _, _ ⟩;
  · exact continuous_const;
  · refine' ⟨ fun _ => zeroStream, _, _ ⟩ <;> norm_num [ MinFun ];
    · exact continuousOn_const;
    · simp +decide [ MinDom ];
      simp +decide [ PointedGluingSet ]

-- /-- **Lemma (Pgluingaslowerbound).**
-- hclopen hypothesis is not used,
-- check the proof in the memoir to see
-- if we can drop this assumption-/
-- theorem pointedGluing_lower_bound_lemma'
--     {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
--     {B : Type*} [TopologicalSpace B] [MetrizableSpace B]
--     (f : A → B) (hf : Continuous f)
--     (C D : ℕ → Set (ℕ → ℕ))
--     (g : ∀ n, C n → D n)
--     (x : A)
--     (An : ℕ → Set A)
--     (hsep : ∀ n, f x ∉ closure (f '' (An n)))
--     (hrelclop : IsRelativeClopenPartition (fun m => f '' (An m)))
--     (hconv : SetsConvergeTo An x)
--     (hred : ∀ n, ContinuouslyReduces
--       (fun (z : C n) => (g n z : ℕ → ℕ))
--       (f ∘ (Subtype.val : An n → A))) :
--     ContinuouslyReduces
--       (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
--       f := by
--   -- Extract hpart and hpart_open from hrelclop
--   have hpart : ∀ m n, m ≠ n → Disjoint (f '' (An m)) (f '' (An n)) :=
--     hrelclop.1
--   have hpart_open : ∀ n, IsOpen
--       ((Subtype.val : (⋃ j, f '' (An j)) → B) ⁻¹' (f '' (An n))) :=
--     hrelclop.2
--   -- Extract σ_n and τ_n from hred
--   have hred' : ∀ n, ∃ (sn : C n → An n) (tn : B → ℕ → ℕ),
--       Continuous sn ∧
--       ContinuousOn tn (Set.range ((f ∘ (Subtype.val : An n → A)) ∘ sn)) ∧
--       ∀ z : C n, (g n z : ℕ → ℕ) = tn (f (sn z).val) := by
--     intro n; obtain ⟨sn, hsn, tn, htn, heqn⟩ := hred n; exact ⟨sn, tn, hsn, htn, heqn⟩
--   choose σ_n τ_n hσ_n hτ_n hτ_n_eq using hred'
--   -- Define σ and τ
--   let σ : PointedGluingSet C → A := fun z =>
--     if h : z.val = zeroStream then x
--     else (σ_n (firstNonzero z.val)
--       ⟨stripZerosOne (firstNonzero z.val) z.val,
--        strip_mem_of_pointedGluingSet C z h⟩).val
--   have σ_cont: Continuous σ := by
--     apply sufficient_cond_continuity σ {z : PointedGluingSet C | z.val ≠ zeroStream}
--     · -- U is open
--       exact isOpen_compl_singleton.preimage continuous_subtype_val
--     · -- Continuity of σ on U
--       -- On U, σ z = (σ_n (firstNonzero z.val) ⟨stripZerosOne _ z.val, _⟩).val
--       -- The pieces {z ∈ U | firstNonzero z.val = n} form a relative clopen partition of U
--       -- On each piece, σ = Subtype.val ∘ σ_n n ∘ ⟨stripZerosOne n ∘ Subtype.val, _⟩
--       -- which is continuous.
--       rw [continuousOn_iff_continuous_restrict]
--       apply continuous_of_relativeClopenPartition_seq
--         (A := fun n => {z : {z : PointedGluingSet C | z.val ≠ zeroStream} |
--           firstNonzero z.val.val = n})
--       · -- IsRelativeClopenPartition
--         constructor
--         · intro m n hmn
--           simp [Set.disjoint_left]
--           intro z hm hn
--           exact hmn (hm.symm.trans hn)
--         · intro n
--           apply isOpen_compl_singleton.preimage
--           apply continuous_subtype_val.comp continuous_subtype_val
--           -- firstNonzero is locally constant on each piece
--           sorry
--       · intro n
--         -- On piece n: σ z = (σ_n n ⟨stripZerosOne n z.val.val, _⟩).val
--         apply Continuous.comp continuous_subtype_val
--         apply hσ_n n |>.comp
--         apply continuous_subtype_mk
--         apply continuous_subtype_val.comp continuous_subtype_val
--     · -- On Uᶜ (z = zeroStream): σ z = x, constant
--       apply (continuousOn_const (c := x)).congr
--       intro z hz
--       simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
--       show σ z = x
--       exact dif_pos hz
--     · -- Sequential: zk → z₀ with zk ≠ zeroStream and z₀ = zeroStream
--       -- Need: σ (zk k) → σ z₀ = x
--       intro zk z₀ hzk_ne hz₀ htendsto
--       simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz₀
--       simp only [σ, dif_pos hz₀]
--       -- Need: σ (zk k) → x
--       -- σ (zk k) = (σ_n (firstNonzero (zk k).val) z').val ∈ An (firstNonzero (zk k).val)
--       -- and An n → x by hconv (SetsConvergeTo)
--       -- and firstNonzero (zk k).val → ∞ as zk k → zeroStream
--       rw [tendsto_nhds]
--       intro U hU hxU
--       -- Find N with An n ⊆ U for all n ≥ N
--       obtain ⟨N, hN⟩ := hconv U hU hxU
--       -- Find M with firstNonzero (zk k).val ≥ N for all k ≥ M
--       -- because zk k → zeroStream means zk k agrees with zeroStream on Finset.range N eventually
--       have hcyl_nhd : {z : PointedGluingSet C | z.val ∈ nbhd zeroStream N} ∈ nhds z₀ := by
--         apply continuous_subtype_val.continuousAt.preimage_mem_nhds
--         apply (baire_nbhd_isClopen zeroStream N).isOpen.mem_nhds
--         simp [nbhd, hz₀]
--       obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
--         (htendsto.eventually (Filter.eventually_of_mem hcyl_nhd fun _ h => h))
--       apply Filter.eventually_atTop.mpr ⟨M, fun k hk => ?_⟩
--       -- σ (zk k) ∈ An (firstNonzero (zk k).val)
--       have hσ_mem : σ (zk k) ∈ An (firstNonzero (zk k).val) := by
--         simp only [σ, dif_neg (hzk_ne k)]
--         exact (σ_n (firstNonzero (zk k).val)
--           ⟨stripZerosOne _ (zk k).val,
--           strip_mem_of_pointedGluingSet C (zk k) (hzk_ne k)⟩).prop
--       -- firstNonzero (zk k).val ≥ N
--       have hfnz_ge : N ≤ firstNonzero (zk k).val := by
--         by_contra hlt
--         push_neg at hlt
--         have hzk_nbhd := hM k hk
--         simp only [Set.mem_setOf_eq, nbhd] at hzk_nbhd
--         have heq : (zk k).val (firstNonzero (zk k).val) = 0 :=
--           by simpa [zeroStream] using
--             hzk_nbhd (firstNonzero (zk k).val) (Finset.mem_range.mpr hlt)
--         have firstNonzero_val_ne {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
--             z (firstNonzero z) ≠ 0 := by
--           have hex : ∃ i, z i ≠ 0 := by
--             by_contra hall
--             push_neg at hall
--             exact hz (funext fun i => by simp [zeroStream, hall i])
--           simp only [firstNonzero, dif_pos hex]
--           exact Nat.find_spec hex
--         exact absurd heq (firstNonzero_val_ne (hzk_ne k))
--       -- An (firstNonzero (zk k).val) ⊆ U since firstNonzero (zk k).val ≥ N
--       exact hN (firstNonzero (zk k).val) hfnz_ge hσ_mem
--   -- τi : (⋃ n, f '' (An n)) → ℕ picks the unique index
--   -- This is continuous by continuous_of_relativeClopenPartition_seq
--   -- since on each piece f '' (An n) it is the constant function n.
--   let In : ℕ → Set B := fun n => range ((f ∘ Subtype.val) ∘ σ_n n)
--   have h_refine : ∀ n, In n ⊆ f '' (An n) := by
--     intro n
--     -- In n is the range of (f ∘ Subtype.val ∘ σ_n n)
--     rintro y ⟨z, rfl⟩
--     -- We need to show y ∈ f '' An n
--     -- y is f (σ_n n z).val
--     use (σ_n n z).val
--     constructor
--     · -- The property of being in An n is the property of the subtype
--       exact (σ_n n z).prop
--     · -- The value matches by definition
--       rfl
--   have h_Indisjoint : ∀ n m, n ≠ m → Disjoint (In n) (In m) := by
--     intro n m hne
--     have h_disjoint : Disjoint (f '' (An n)) (f '' (An m)) := hpart n m hne
--     exact h_disjoint.mono (h_refine n) (h_refine m)
--   have hrelclop' : IsRelativeClopenPartition In := RelativeClopenPartition_stable_by_refine hrelclop h_refine
--   let τi : (⋃ n, In n) → ℕ := fun y =>
--     Classical.choose (Set.mem_iUnion.mp y.prop)
--   have hτi_cont : Continuous τi := by
--     apply continuous_of_relativeClopenPartition_seq hrelclop'
--     intro n
--     apply continuous_const.congr
--     intro ⟨y, hy⟩
--     dsimp [τi]
--     generalize_proofs h_mem
--     set m := Classical.choose h_mem
--     have hm : y ∈ In m := Classical.choose_spec h_mem
--     by_contra hne
--     -- hne : n ≠ m
--     -- hm  : y ∈ In m (from choose_spec)
--     -- hy  : y ∈ In n (from the partition piece)
--     -- We use the disjointness hypothesis:
--     have h_Idisjoint : Disjoint (In n) (In m) := h_Indisjoint n m hne
--     exact h_Idisjoint.le_bot ⟨hy, hm⟩
--   -- Now define τ as a composition
--   -- On ⋃ n, In n: τ y = prependZerosOne (τi y) (τ_{τi y} y)
--   -- Outside: τ y = zeroStream
--   let τ : (⋃ n, In n)  → ℕ → ℕ := fun y =>
--     let yi : ⋃ n, In n := y
--     prependZerosOne (τi yi) (τ_n (τi yi) y)
--     -- else zeroStream
--   -- This lemma allows us to simplify τi on the pieces
--   have hτi_n : ∀ (y : ⋃ n, In n) (n : ℕ) (hy : y.val ∈ In n), τi y = n := by
--     intro y n hy
--     dsimp [τi]
--     generalize_proofs h_mem
--     set m := Classical.choose h_mem
--     have hm : y.val ∈ In m := Classical.choose_spec h_mem
--     by_contra hne
--     have h_Idisjoint : Disjoint (In m) (In n) := h_Indisjoint m n hne
--     have hy' : y.val ∈ f '' An n := h_refine n hy
--     have hm' : y.val ∈ f '' An m := h_refine m hm
--     exact (hpart m n hne).le_bot ⟨hm', hy'⟩
--   -- Continuity of τ on ⋃ n, In n by composition
--   have h_Ipart : IsRelativeClopenPartition In := by
--     constructor
--     · exact h_Indisjoint
--     · -- We apply the stability theorem we proved earlier
--       intro n
--       exact (RelativeClopenPartition_stable_by_refine hrelclop h_refine).2 n

--   -- Define UI as the union of the In sets for convenience
--   let UI := ⋃ n, In n

--   have hfpart : ∀ n, Continuous (fun x : In n => τ (Set.inclusion (Set.subset_iUnion In n) x)) := by
--     intro n
--     -- Use the lemma hτi_n to show that on piece n, τi is always n
--     have h_eq : ∀ x : In n, τ (Set.inclusion (Set.subset_iUnion In n) x) =
--         prependZerosOne n (τ_n n x.val) := by
--       intro x
--       dsimp [τ]
--       rw [hτi_n (Set.inclusion (Set.subset_iUnion In n) x) n x.2]
--     -- Now show the right-hand side is continuous
--     -- We break this down: x ↦ x.val is continuous, τ_n n is continuous on its range,
--     -- and prependZerosOne is continuous.
--     have h_cont_rhs : Continuous (fun x : In n => prependZerosOne n (τ_n n x.val)) := by
--       apply (continuous_prependZerosOne n).comp
--       -- τ_n n is ContinuousOn (In n). We use ContinuousOn.comp_continuous
--       -- with the continuous inclusion of the subtype.
--       apply ContinuousOn.comp_continuous (hτ_n n)
--       · exact continuous_subtype_val
--       · intro x; exact x.2 -- Proof that x.val is in the range (In n)

--     -- 2. Use Continuous.congr to transfer continuity to the LHS
--     exact Continuous.congr h_cont_rhs (fun x => (h_eq x).symm)

--   -- Now this should unify correctly
--   have hτ_cont : Continuous τ := continuous_of_relativeClopenPartition_seq h_Ipart hfpart
--   let τ_global : B → (ℕ → ℕ) := fun y =>
--     if h : y ∈ UI then τ ⟨y, h⟩ else zeroStream
--   have h_incl : ∀ z, z ∈ {y : PointedGluingSet C | y.val ≠ zeroStream} →
--             f (σ z) ∈ UI := by
--           intro z hz
--           simp only [Set.mem_setOf_eq] at hz
--           show f (σ z) ∈ ⋃ n, In n
--           rw [Set.mem_iUnion]
--           refine ⟨firstNonzero z.val, ?_⟩
--           -- Goal: f (σ z) ∈ In (firstNonzero z.val)
--           -- In n = Set.range ((f ∘ Subtype.val) ∘ σ_n n)
--           show f (σ z) ∈ Set.range ((f ∘ Subtype.val) ∘ σ_n (firstNonzero z.val))
--           simp only [σ, dif_neg hz, Function.comp, Set.mem_range]
--           exact ⟨⟨stripZerosOne _ z.val, strip_mem_of_pointedGluingSet C z hz⟩, rfl⟩
--   refine ⟨σ, σ_cont ,τ_global, ?_, ?_⟩
--   · -- ContinuousOn τ_global on Set.range (fun z => f (σ z))
--     -- Step 1: show that range(f ∘ σ) ⊆ UI ∪ {f x} and derive ContinuousOn
--     -- from Continuous of the composition z ↦ τ_global (f (σ z)).
--     --
--     -- Key fact: U = {z | z.val ≠ zeroStream} = σ⁻¹(⋃ n, An n)
--     -- which maps via f into ⋃ n, f '' (An n) ⊇ ⋃ n, In n = UI
--     have hcomp : Continuous (fun z : PointedGluingSet C => τ_global (f (σ z))) := by
--       apply sufficient_cond_continuity _
--         {z : PointedGluingSet C | z.val ≠ zeroStream}
--       · -- U is open
--         apply isOpen_compl_singleton.preimage continuous_subtype_val
--       · -- Continuity on U: factors as hτ_cont ∘ (lift to UI) ∘ f ∘ σ
--         apply ContinuousOn.congr
--         · intro z hz
--           simp only [Set.mem_setOf_eq] at hz
--           apply ContinuousAt.continuousWithinAt
--           -- τ_global (f (σ z)) = τ ⟨f (σ z), h_incl z hz⟩
--           -- = (τ ∘ (fun w => ⟨f (σ w), h_incl w (...)⟩)) z
--           -- Factor: use that the map to the subtype is continuous
--           have hfσ : ContinuousAt (f ∘ σ) z := (hf.comp σ_cont).continuousAt
--           -- Lift to subtype using the filter
--           have hlift : ContinuousAt (fun w : PointedGluingSet C =>
--               (⟨f (σ w), h_incl w (Set.mem_setOf.mpr (by
--                 -- can't use hz here for other w
--                 sorry))⟩ : UI)) z := by
--             sorry
--           exact hτ_cont.continuousAt.comp hlift
--         · intro z hz
--           simp only [Set.mem_setOf_eq] at hz
--           simp only [τ_global, dif_pos (h_incl z hz)]
--           rfl
--       · -- On Uᶜ: z = zeroStream, τ_global (f (σ z)) = zeroStream
--         apply (continuousOn_const (c := zeroStream)).congr
--         intro z hz
--         simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz
--         have hσz : σ z = x := by simp [σ, dif_pos hz]
--         have hfx_notUI : f x ∉ UI := fun hmem => by
--           obtain ⟨n, zn, hzn⟩ := Set.mem_iUnion.mp hmem
--           exact hsep n (subset_closure ⟨(σ_n n zn).val, (σ_n n zn).prop, hzn⟩)
--         simp [τ_global, hσz, dif_neg hfx_notUI]
--       · -- Sequential condition: zk → z₀ with zk ≠ zeroStream and z₀ = zeroStream
--         -- Need: τ_global (f (σ (zk n))) → τ_global (f (σ z₀)) = zeroStream
--         intro zk z₀ hzk_ne hz₀ htendsto
--         simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hz₀
--         -- τ_global (f (σ z₀)) = zeroStream
--         have hσz₀ : σ z₀ = x := by simp [σ, dif_pos hz₀]
--         have hfx_notUI : f x ∉ UI := fun hmem => by
--           obtain ⟨n, zn, hzn⟩ := Set.mem_iUnion.mp hmem
--           exact hsep n (subset_closure ⟨(σ_n n zn).val, (σ_n n zn).prop, hzn⟩)
--         simp only [hσz₀, τ_global, dif_neg hfx_notUI]
--         -- Need: τ_global (f (σ (zk n))) → zeroStream
--         -- For each k, zk k ≠ zeroStream, so f (σ (zk k)) ∈ UI
--         -- and τ_global (f (σ (zk k))) = τ ⟨f (σ (zk k)), _⟩
--         --   = prependZerosOne (τi _) (τ_n (τi _) _)
--         -- where τi = firstNonzero (zk k).val
--         -- As zk k → zeroStream, firstNonzero (zk k).val → ∞
--         -- so prependZerosOne n _ → zeroStream
--         --
--         -- The key: σ (zk k) ∈ An (firstNonzero (zk k).val) (by construction of σ)
--         -- and An n → x (by hconv)
--         -- So σ (zk k) → x by SetsConvergeTo.
--         -- But we need τ_global (f (σ (zk k))) → zeroStream.
--         -- Use: τ_global (f (σ (zk k))) = prependZerosOne (firstNonzero (zk k).val) _
--         -- and firstNonzero (zk k).val → ∞ since zk k → zeroStream
--         -- and prependZerosOne n y → zeroStream as n → ∞ (uniformly in y).
--         --
--         -- Step 1: σ (zk k) ∈ An (firstNonzero (zk k).val) for all k
--         have hσ_in_An : ∀ k, σ (zk k) ∈ An (firstNonzero (zk k).val) := by
--           intro k
--           simp only [σ, dif_neg (hzk_ne k)]
--           -- σ (zk k) = (σ_n n z').val where z' : C n and σ_n n : C n → An n
--           -- so (σ_n n z').val ∈ An n by definition of the subtype
--           exact (σ_n (firstNonzero (zk k).val)
--             ⟨stripZerosOne _ (zk k).val,
--              strip_mem_of_pointedGluingSet C (zk k) (hzk_ne k)⟩).prop
--         -- Step 2: firstNonzero (zk k).val → ∞
--         -- because zk k → zeroStream means (zk k).val → zeroStream in ℕ→ℕ
--         -- and zeroStream i = 0 for all i, so (zk k).val i → 0
--         -- and (zk k).val ≠ zeroStream means firstNonzero (zk k).val is well-defined
--         -- and firstNonzero z ≥ n iff z agrees with zeroStream on first n coords
--         -- i.e. iff z ∈ nbhd zeroStream n
--         -- zk k → zeroStream means for all N, eventually zk k ∈ nbhd zeroStream N (as elements of PointedGluingSet C)
--         -- which means eventually (zk k).val ∈ nbhd zeroStream N (in ℕ→ℕ)
--         -- which means eventually firstNonzero (zk k).val ≥ N
--         have hfnz_tendsto : Filter.Tendsto
--             (fun k => firstNonzero (zk k).val) Filter.atTop Filter.atTop := by
--           rw [Filter.tendsto_atTop]
--           intro N
--           -- zk → z₀ = zeroStream, so zk k ∈ cyl N eventually (in PointedGluingSet)
--           -- i.e. (zk k).val agrees with zeroStream on Finset.range N
--           -- i.e. firstNonzero (zk k).val ≥ N
--           have hcyl_nbhd : {z : PointedGluingSet C | z.val ∈ nbhd zeroStream N} ∈
--               nhds z₀ := by
--             apply continuous_subtype_val.continuousAt.preimage_mem_nhds
--             exact (baire_nbhd_isClopen zeroStream N).isOpen.mem_nhds (by simp [nbhd, hz₀])
--           obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
--             (Filter.Tendsto.eventually htendsto hcyl_nbhd)
--           refine Filter.eventually_atTop.mpr ⟨M, fun k hk => ?_⟩
--           have hzk_nbhd := hM k hk
--           simp only [nbhd, Set.mem_setOf_eq] at hzk_nbhd
--           -- hzk_nbhd : ∀ i ∈ Finset.range N, (zk k).val i = zeroStream i
--           -- i.e. (zk k).val i = 0 for all i < N
--           -- Need: N ≤ firstNonzero (zk k).val
--           -- Proof by contradiction: if firstNonzero (zk k).val < N, then
--           -- (zk k).val (firstNonzero (zk k).val) = 0 by hzk_nbhd,
--           -- but firstNonzero finds the first NON-zero position.
--           by_contra hlt
--           push_neg at hlt
--           -- (zk k).val agrees with zeroStream on Finset.range N,
--           -- so on all positions < N, and in particular at firstNonzero (zk k).val < N
--           -- But firstNonzero returns a position where the value differs from zeroStream
--           -- i.e. (zk k).val (firstNonzero (zk k).val) ≠ zeroStream (firstNonzero (zk k).val)
--           have heq : (zk k).val (firstNonzero (zk k).val) =
--               zeroStream (firstNonzero (zk k).val) :=
--             hzk_nbhd (firstNonzero (zk k).val) (Finset.mem_range.mpr hlt)
--           have hzero : zeroStream (firstNonzero (zk k).val) = 0 := rfl
--           rw [hzero] at heq
--           -- heq : (zk k).val (firstNonzero (zk k).val) = 0
--           -- But firstNonzero (zk k).val is the first index where (zk k).val ≠ zeroStream
--           -- So (zk k).val (firstNonzero (zk k).val) ≠ 0
--           -- The value at firstNonzero is nonzero by definition
--           apply hzk_ne k
--           ext i
--           simp only [zeroStream]
--           have firstNonzero_val_ne {z : ℕ → ℕ} (hz : z ≠ zeroStream) :
--               z (firstNonzero z) ≠ 0 := by
--             have hex : ∃ i, z i ≠ 0 := by
--               by_contra hall
--               push_neg at hall
--               exact hz (funext fun i => by simp [zeroStream, hall i])
--             simp only [firstNonzero, dif_pos hex]
--             exact Nat.find_spec hex
--           exact absurd heq (firstNonzero_val_ne (hzk_ne k))
--         -- Step 3: τ_global (f (σ (zk k))) = prependZerosOne (firstNonzero (zk k).val) _
--         -- and this → zeroStream because prependZerosOne n _ → zeroStream
--         apply tendsto_nhds.mpr
--         intro V hV hzero_V
--         obtain ⟨N, hN⟩ := nbhd_basis zeroStream V hV hzero_V
--         -- Eventually firstNonzero (zk k).val ≥ N
--         obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
--           (Filter.tendsto_atTop.mp hfnz_tendsto N)
--         refine Filter.eventually_atTop.mpr ⟨M, fun k hk => hN ?_⟩
--         -- Show τ_global (f (σ (zk k))) ∈ nbhd zeroStream N
--         have hmem_UI : f (σ (zk k)) ∈ UI :=
--           h_incl (zk k) (hzk_ne k)
--         rw [dif_pos hmem_UI]
--         simp only [τ]
--         -- τi ⟨f (σ (zk k)), hmem_UI⟩ = firstNonzero (zk k).val
--         rw [hτi_n ⟨f (σ (zk k)), hmem_UI⟩ (firstNonzero (zk k).val)
--           (by exact ⟨⟨stripZerosOne _ (zk k).val,
--                 strip_mem_of_pointedGluingSet C (zk k) (hzk_ne k)⟩, rfl⟩)]
--         -- prependZerosOne (firstNonzero (zk k).val) _ ∈ nbhd zeroStream N
--         intro i hi
--         simp only [nbhd, Finset.mem_range] at hi
--         -- prependZerosOne n y i = 0 for i < n
--         -- and N ≤ firstNonzero (zk k).val (by hM k hk)
--         -- so i < N ≤ firstNonzero (zk k).val, hence i < firstNonzero (zk k).val
--         apply prependZerosOne_eq_zero
--         exact hi.trans_le (hM k hk)
--     -- Derive ContinuousOn on the range from the continuous composition
--     rw [continuousOn_iff_continuous_restrict]
--     rintro ⟨y, z, rfl⟩
--     rfl
--   · -- Goal 2: ∀ z, PointedGluingFun C D g z = τ_global (f (σ z))
--     intro z
--     by_cases h : z.val = zeroStream
--     · -- z = zeroStream: PointedGluingFun = zeroStream and τ_global (f x) = zeroStream
--       simp only [σ, dif_pos h]
--       have hfx_notUI : f x ∉ UI := by
--         intro hmem
--         obtain ⟨n, zn, hzn⟩ := Set.mem_iUnion.mp hmem
--         exact hsep n (subset_closure ⟨(σ_n n zn).val, (σ_n n zn).prop, hzn⟩)
--       simp only [τ_global, dif_neg hfx_notUI]
--       -- PointedGluingFun C D g ⟨zeroStream, _⟩ = zeroStream
--       exact PointedGluingFun_zero C D g z h
--     · -- z ≠ zeroStream: use hτ_n_eq
--       set n := firstNonzero z.val
--       set z' := ⟨stripZerosOne n z.val, strip_mem_of_pointedGluingSet C z h⟩
--       simp only [σ, dif_neg h]
--       -- σ z = (σ_n n z').val
--       -- f (σ z) = f (σ_n n z').val ∈ In n ⊆ UI
--       have hfσ_UI : f (σ_n n z').val ∈ UI := by
--         apply Set.mem_iUnion.mpr
--         exact ⟨n, z', rfl⟩
--       simp only [τ_global, dif_pos hfσ_UI]
--       -- τ ⟨f (σ_n n z').val, _⟩ = prependZerosOne (τi _) (τ_n (τi _) _)
--       -- and τi gives n (since f (σ_n n z').val ∈ In n)
--       simp only [τ]
--       rw [hτi_n ⟨f (σ_n n z').val, hfσ_UI⟩ n (by exact ⟨z', rfl⟩)]
--       -- Now: prependZerosOne n (τ_n n (f (σ_n n z').val))
--       -- = PointedGluingFun C D g z
--       -- by definition of PointedGluingFun and hτ_n_eq
--       rw [← hτ_n_eq n z']
--       exact PointedGluingFun_eq C D g z h n z' rfl rfl


/-- **Proposition (Pgluingaslowerbound2). Pointed gluing as lower bound.**

Note: The original statement had the equation direction `f (σ z) = τ (g i z)` in hloc,
which is incorrect for the intended mathematical content. The correct direction
(matching `pgl_lower_bound_step` and the mathematical proof) is
`(g i z : ℕ → ℕ) = τ (f (σ z))`, which says that g_i reduces to f locally.
The statement below uses the corrected equation direction. -/
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
        (∀ z, (g i z : ℕ → ℕ) = τ (f (σ z))) ∧
        ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
        (∀ z, σ z ∈ U) ∧
        f x ∉ closure (Set.range (fun z => f (σ z)))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  -- Cylinder neighborhoods of x in A
  let cyl : ℕ → Set A := fun n => nbhd' A x n
  -- Cylinder neighborhoods of f x in ℕ→ℕ
  let cylfx : ℕ → Set (ℕ → ℕ) := fun n => nbhd (f x) n
  -- Basic facts about cylinders
  have hcyl_clopen : ∀ n, IsClopen (cyl n) := fun n =>
    baire_nbhd'_isClopen A x n
  have hcyl_open : ∀ n, IsOpen (cyl n) := fun n =>
    (hcyl_clopen n).isOpen
  have hx_cyl : ∀ n, x ∈ cyl n := fun n => by
    simp [cyl, nbhd']
  have hcylfx_clopen : ∀ n, IsClopen (cylfx n) := fun n =>
    baire_nbhd_isClopen (f x) n
  have hcylfx_open : ∀ n, IsOpen (cylfx n) := fun n =>
    (hcylfx_clopen n).isOpen
  have hfx_cylfx : ∀ n, f x ∈ cylfx n := fun n => by
    simp [cylfx, nbhd]
  -- Neighborhood basis at x in A
  have hbasis_x : ∀ U : Set A, IsOpen U → x ∈ U → ∃ n, cyl n ⊆ U :=
    nbhd_basis' A x
  -- Neighborhood basis at f x in ℕ→ℕ
  have hbasis_fx : ∀ U : Set (ℕ → ℕ), IsOpen U → f x ∈ U → ∃ n, cylfx n ⊆ U :=
    nbhd_basis (f x)
  -- Helper: find m such that closure S ∩ cylfx m = ∅, given f x ∉ closure S
  have find_m : ∀ S : Set (ℕ → ℕ), f x ∉ closure S →
      ∃ m, closure S ∩ cylfx m = ∅ := by
    intro S hclos
    have hopen : IsOpen (closure S)ᶜ := isClosed_closure.isOpen_compl
    have hfx_mem : f x ∈ (closure S)ᶜ := hclos
    obtain ⟨m, hm⟩ := hbasis_fx _ hopen hfx_mem
    exact ⟨m, by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hy_clos hy_cyl
      exact hm hy_cyl hy_clos⟩
  -- Helper: find l such that f '' cyl l ⊆ cylfx m
  have find_l : ∀ m : ℕ, ∃ l, ∀ a ∈ cyl l, f a ∈ cylfx m := by
    intro m
    have hpre : IsOpen (f ⁻¹' cylfx m) := (hcylfx_open m).preimage hf
    have hx_pre : x ∈ f ⁻¹' cylfx m := hfx_cylfx m
    obtain ⟨l, hl⟩ := hbasis_x _ hpre hx_pre
    exact ⟨l, fun a ha => hl ha⟩
  -- ----------------------------------------------------------------
  -- Build the sequence (σ n, τ n) with data (k n, l n, m n) by induction
  -- Invariant:
  --   k n ≥ n              (for SetsConvergeTo)
  --   l n ≥ n + 1          (for next step's k ≥ n+1)
  --   σ n z ∈ cyl (k n)
  --   closure(range(f∘σ n)) ∩ cylfx (m n) = ∅
  --   ∀ a ∈ cyl (l n), f a ∈ cylfx (m n)   (threading disjointness)
  -- ----------------------------------------------------------------
  -- We use a recursive construction via Nat.rec on a bundled type.
  -- To avoid defining structures inside a tactic block, we use a Σ-type.
  -- PackedData n = Σ k l m, (C n → A) × ((ℕ→ℕ)→(ℕ→ℕ)) × proofs...
  -- For readability, we use a named predicate.
  let GoodData : ∀ n : ℕ, (k l m : ℕ) → (C n → A) → ((ℕ → ℕ) → ℕ → ℕ) → Prop :=
    fun n k l m σ τ =>
      k ≥ n ∧ l ≥ n + 1 ∧
      Continuous σ ∧
      (∀ z, (g n z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ cyl k) ∧
      closure (Set.range (fun z => f (σ z))) ∩ cylfx m = ∅ ∧
      (∀ a ∈ cyl l, f a ∈ cylfx m)
  have buildData : ∀ n, ∃ k l m, ∃ (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      GoodData n k l m σ τ := by
    intro n
    induction n with
    | zero =>
      obtain ⟨σ, τ, hσc, hcomm, hτc, _, hclos⟩ :=
        hloc 0 Set.univ isOpen_univ (Set.mem_univ x)
      obtain ⟨m, hm⟩ := find_m _ hclos
      obtain ⟨l₀, hl₀⟩ := find_l m
      refine ⟨0, max l₀ 1, m, σ, τ, le_refl _, le_max_right _ _, hσc, hcomm,
        hτc, fun z => by simp [cyl, nbhd'], hm, fun a ha => hl₀ a ?_⟩
      intro i hi
      exact ha i (Finset.range_mono (le_max_left l₀ 1) hi)
    | succ n ih =>
      obtain ⟨k, l, m, σ_n, τ_n, hk, hl, hσc_n, hcomm_n, hτc_n,
               hσcyl_n, hclosure_n, hfl_n⟩ := ih
      -- Use U = cyl l for step n+1
      obtain ⟨σ', τ', hσc', hcomm', hτc', hσU', hclos'⟩ :=
        hloc (n + 1) (cyl l) (hcyl_open l) (hx_cyl l)
      obtain ⟨m', hm'⟩ := find_m _ hclos'
      obtain ⟨l₀', hl₀'⟩ := find_l m'
      refine ⟨l, max l₀' (n + 2), m', σ', τ', hl, le_max_right _ _, hσc',
        hcomm', hτc', hσU', hm', fun a ha => hl₀' a ?_⟩
      intro i hi
      exact ha i (Finset.range_mono (le_max_left l₀' (n + 2)) hi)
  -- Extract components
  choose kseq lseq mseq σseq τseq hgood using buildData
  -- Unpack GoodData for each n
  have hk    : ∀ n, kseq n ≥ n                 := fun n => (hgood n).1
  have hl    : ∀ n, lseq n ≥ n + 1             := fun n => (hgood n).2.1
  have hσc   : ∀ n, Continuous (σseq n)         := fun n => (hgood n).2.2.1
  have hcomm : ∀ n z, (g n z : ℕ → ℕ) = τseq n (f (σseq n z)) :=
                                                    fun n => (hgood n).2.2.2.1
  have hτc   : ∀ n, ContinuousOn (τseq n)
      (Set.range (fun z => f (σseq n z)))        := fun n => (hgood n).2.2.2.2.1
  have hσcyl : ∀ n z, σseq n z ∈ cyl (kseq n)  := fun n => (hgood n).2.2.2.2.2.1
  have hclos : ∀ n, closure (Set.range (fun z => f (σseq n z))) ∩
      cylfx (mseq n) = ∅                        := fun n => (hgood n).2.2.2.2.2.2.1
  have hfl   : ∀ n a, a ∈ cyl (lseq n) → f a ∈ cylfx (mseq n) :=
                                                    fun n => (hgood n).2.2.2.2.2.2.2
  -- ----------------------------------------------------------------
  -- The threading lemma: f(σseq q z) ∈ cylfx (mseq p) for all q > p
  -- Proof: σseq (p+1) z ∈ cyl (lseq p) so f(σseq (p+1) z) ∈ cylfx (mseq p).
  -- For q > p+1: kseq q ≥ q > p+1 ≥ lseq p (since lseq p ≥ p+1),
  -- so cyl (kseq q) ⊆ cyl (lseq p) (cyl is antitone: larger index = smaller set).
  -- Hence σseq q z ∈ cyl (kseq q) ⊆ cyl (lseq p), so f(σseq q z) ∈ cylfx (mseq p).
  have cyl_antitone : ∀ m n : ℕ, m ≤ n → cyl n ⊆ cyl m := by
    intro m n hmn a ha i hi
    exact ha i (Finset.range_mono hmn hi)
  have threading : ∀ p q : ℕ, p < q → ∀ z, f (σseq q z) ∈ cylfx (mseq p) := by
    intro p q hpq z
    apply hfl p
    apply cyl_antitone (lseq p) (kseq q)
    · -- lseq p ≤ kseq q: lseq p ≤ p+1 ≤ q ≤ kseq q... wait: hl p : lseq p ≥ p+1
      -- and hk q : kseq q ≥ q, and q > p so q ≥ p+1 ≥ lseq p? No: lseq p ≥ p+1.
      -- We need lseq p ≤ kseq q. We have kseq q ≥ q ≥ p+1.
      -- But lseq p ≥ p+1 as well, so we can't conclude lseq p ≤ kseq q in general.
      -- FIX: strengthen the invariant so that kseq (n+1) = lseq n.
      -- This holds BY CONSTRUCTION: in the succ case we set k = l (previous l).
      -- So kseq (n+1) = lseq n for all n.
      -- Let's prove this from how buildData was constructed.
      sorry -- kseq (p+1) = lseq p, and kseq is increasing: kseq q ≥ kseq (p+1) = lseq p
    · exact hσcyl q z
  -- ----------------------------------------------------------------
  -- Define An and apply pointedGluing_lower_bound_lemma'
  -- ----------------------------------------------------------------
  let An : ℕ → Set A := fun n => Set.range (σseq n)
  let σ_n : ∀ n, C n → An n := fun n z => ⟨σseq n z, Set.mem_range_self z⟩
  apply pointedGluing_lower_bound_lemma' f hf C D g x An
  · -- hclopen: An n is clopen
    intro n
    -- C n is clopen in ℕ→ℕ, σseq n is continuous, so range σseq n is clopen
    -- (the range of a continuous injective map from a clopen is clopen)
    -- If C n is not clopen, we need a different argument.
    -- In our setting: σseq n maps C n → A, and range(σseq n) = An n.
    -- Since σseq n is continuous and C n is a subtype of ℕ→ℕ (Polish/clopen),
    -- and A is a subspace, this needs the relevant lemma from the codebase.
    sorry
  · -- hsep: f x ∉ closure (f '' An n)
    sorry
  · -- hpart: Disjoint (f '' An p) (f '' An q) for p ≠ q
    sorry
  · -- hconv: SetsConvergeTo An x
    sorry
  -- · -- hred: ContinuouslyReduces (g n) (f ∘ val ∘ σ_n n)
  --   intro n
  --   exact ⟨σ_n n, τseq n, (hσc n).subtype_mk _,
  --          fun z => hcomm n z,
  --          by convert hτc n using 2; simp [σ_n, An]⟩

-- **Proposition (Minfunctions). Minimum functions.**

-- Warning MinFun α has CB rank α+1!
/--
PROVIDED SOLUTION

For $\alpha=0$, note that MinFun 0 continuously reduces to any non\-empty function.
So suppose that $\alpha>0$ and that the statement holds for every $\beta<\alpha$.

Take a simple function $f\in\sC_{\alpha+1}$ and let $y\in\im f$ be the distinguished point of $f$.
Seeing that $\Minimalfct{\alpha+1}$ is a pointed gluing, we seek to apply \cref{Pgluingaslowerbound2} for some point $x\in\CB_\alpha(f)$. Let $U\ni x$ be any open set of $\dom f$.
Notice first that as $x\in\CB_\alpha(f)$ and $x\in U$ we get that $f_U=f\restr{U}$ is simple and $\CB(f_U)=\alpha+1$ by \cref{CBbasics0}~\cref{CBbasicsfromJSL2}.
Note that by \cref{CBrankofPgluingofregularsequence2simple} the sequence $(\CB(\ray{f_{U}}{y,n}))_n$ is regular of supremum $\alpha$. If $\alpha=\beta+1$ is successor, then there exists $N$ such that $\alpha=\CB(\ray{f_U}{y,N})$. By the induction hypothesis combined with our first remark, we get $\Minimalfct{\alpha}\leq \ray{f_{U}}{y,N}$.
Notice that if $(\sigma, \tau)$ witnesses this reduction then both $\im \sigma \subseteq U$ and $\overline{\im f\sigma}\subseteq \ray{B}{y,N}$ hold. This ensures that $\Minimalfct{\alpha+1}=\pgl \Minimalfct{\alpha} \leq f$ by \cref{Pgluingaslowerbound2}.


If $\alpha$ is limit, for all $\beta< \alpha$ there exists $N$ such that $\beta+1\leq \CB(\ray{f_{U}}{y,N})< \alpha$. So by the induction hypothesis combined with our first remark, we get $\Minimalfct{\beta+1}\leq \ray{f_{U}}{y,N}$.
So similarly as in the successor case, we get $\Minimalfct{\alpha+1}=\pgl_{k}\Minimalfct{\beta_k+1}\leq f$, for $(\beta_k)_k$ cofinal in $\alpha$.
-/
lemma minFun_is_minimum_simple
    (α : Ordinal.{0}) (hα : α < omega1)
    (A : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hlevel_ne : (CBLevel f α).Nonempty)
    (hlevel_succ_empty : CBLevel f (Order.succ α) = ∅)
    (h_simple : ∃ y : ℕ → ℕ, ∀ x ∈ CBLevel f α, f x = y) :
      ContinuouslyReduces (MinFun α) f := by
    sorry
  -- induction α using Ordinal.induction with
  -- | h α ih =>
  -- -- Base case: α = 0
  -- -- MinFun 0 = ptgl ∅ ≡ id_{(0)^∞} reduces to any nonempty function
  -- -- ----------------------------------------------------------------
  -- by_cases hα0 : α = 0
  -- · subst hα0
  --   have hne : A.Nonempty := by
  --     obtain ⟨x, hx⟩ := hlevel_ne
  --     sorry
  --   exact minFun_zero_reduces f hne
  -- -- ----------------------------------------------------------------
  -- -- Inductive step: α > 0
  -- -- ----------------------------------------------------------------
  -- -- Pick x ∈ CBLevel f α as the base point for pointedGluing_lower_bound'
  -- obtain ⟨x, hx⟩ := hlevel_ne
  -- -- MinFun α is a pointed gluing, so apply the lower bound criterion
  -- -- The index type for the pointed gluing depends on whether α is successor or limit:
  -- --   α = β+1: MinFun (β+1) = ptgl (MinFun β), index type = ℕ (constant sequence)
  -- --   α limit: MinFun α = ptgl_n (MinFun αₙ), for (αₙ) cofinal in α
  -- apply pointedGluing_lower_bound' f hf C D g x
  -- -- Goal: for each n : ℕ and open U ∋ x, find (σ, τ) reducing the n-th component
  -- -- of MinFun α to f, with im σ ⊆ U and f x ∉ closure(range(f ∘ σ))
  -- intro i U hU hxU
  -- -- ----------------------------------------------------------------
  -- -- f|_U is simple with CB rank α+1
  -- -- ----------------------------------------------------------------
  -- -- CBLevel (f|_U) α = CBLevel f α ∩ U ∋ x (by local_cb_derivative)
  -- have hfU_level : (CBLevel (f ∘ (Subtype.val : U → ℕ → ℕ)) α).Nonempty := by
  --   have hlocal := local_cb_derivative U hU α (f := f)
  --   -- hlocal : Subtype.val '' CBLevel (f ∘ val) α = CBLevel f α ∩ U
  --   refine ⟨⟨x, hxU⟩, ?_⟩
  --   -- Need: ⟨x, hxU⟩ ∈ CBLevel (f ∘ val) α
  --   -- i.e. x ∈ Subtype.val '' CBLevel (f ∘ val) α (then use hlocal)
  --   have hxmem : x ∈ CBLevel f α ∩ U := ⟨hx, hxU⟩
  --   rw [← hlocal] at hxmem
  --   obtain ⟨z, hz, hzval⟩ := hxmem
  --   -- z : U with z.val = x and hz : z ∈ CBLevel (f ∘ val) α
  --   convert hz using 1
  --   exact Subtype.val_injective hzval
  -- -- CBLevel (f|_U) (succ α) = CBLevel f (succ α) ∩ U = ∅ (by local_cb_derivative)
  -- have hfU_succ_empty : CBLevel (f ∘ (Subtype.val : U → ℕ → ℕ)) (Order.succ α) = ∅ := by
  --   have hlocal := local_cb_derivative U hU (Order.succ α) (f := f)
  --   ext z
  --   simp only [Set.mem_empty_iff_false, iff_false]
  --   intro hz
  --   have : z.val ∈ CBLevel f (Order.succ α) ∩ U := by
  --     rw [← hlocal]
  --     exact ⟨z, hz, rfl⟩
  --   rw [hlevel_succ_empty, Set.empty_inter] at this
  --   exact this
  -- -- f|_U is simple with the same distinguished point y
  -- have hfU_simple : ∃ y' : ℕ → ℕ, ∀ z ∈ CBLevel (f ∘ (Subtype.val : U → ℕ → ℕ)) α,
  --     (f ∘ Subtype.val) z = y' := by
  --   refine ⟨y, fun z hz => ?_⟩
  --   -- z ∈ CBLevel (f ∘ val) α means z.val ∈ CBLevel f α (by local_cb_derivative)
  --   have hlocal := local_cb_derivative U hU α (f := f)
  --   have : z.val ∈ CBLevel f α ∩ U := by
  --     rw [← hlocal]; exact ⟨z, hz, rfl⟩
  --   exact hy z.val this.1
  -- -- ----------------------------------------------------------------
  -- -- The rays of f|_U at y have regular CB-ranks with supremum α
  -- -- by Prop 3.10 (CBrankofPgluingofregularsequence2simple)
  -- -- ----------------------------------------------------------------
  -- -- ray f y n = f co-restricted to {z ∈ B | y↾n ⊑ z ∧ y↾(n+1) ⋢ z}
  -- have h_regular : IsRegularSequence (fun n => CBRank (rayFun f y n)) ∧
  --     sSup (Set.range (fun n => CBRank (rayFun f y n))) = α := by
  --   exact CBrankofPgluingofregularsequence2simple f hf_scat α hlevel_ne
  --     hlevel_succ_empty ⟨y, hy⟩
  --   -- (hypothetical name; replace with actual Lean lemma name)
  -- obtain ⟨hreg, hsup⟩ := h_regular
  -- -- ----------------------------------------------------------------
  -- -- Case split: α is successor or limit
  -- -- ----------------------------------------------------------------
  -- rcases Ordinal.zero_or_succ_or_limit α with rfl | ⟨β, rfl⟩ | hlim
  -- · exact absurd rfl hα0
  -- · -- *** Successor case: α = β + 1 ***
  --   -- MinFun (β+1) = ptgl (MinFun β)
  --   -- The rays have CB-ranks with sup = β+1, and the sequence is regular,
  --   -- so since β+1 is a successor, ∃ n with CB(ray f y n) = β+1.
  --   -- Wait: sup = α = β+1 but each αₙ ≤ β (since rays have CB-rank < α+1 = β+2),
  --   -- so actually sup = β, not β+1. Careful: CBRank f = α+1 = β+2,
  --   -- and ray CB-ranks have sup = α = β+1. So rays can have CB-rank β+1.
  --   -- Regular + sup = β+1 (successor) means ∃ n, CB(ray n) = β+1.
  --   have ⟨n, hn⟩ : ∃ n, CBRank (rayFun f y n) = Order.succ β := by
  --     -- regularity + sup = succ β means the sequence reaches succ β
  --     exact hreg.exists_eq_of_succ_sup hsup
  --     -- (hypothetical; replace with actual lemma)
  --   -- Apply IH at β: MinFun β ≤ ray f y n
  --   -- ray f y n has CB rank β+1, is simple (rays of a simple function are simple),
  --   -- and CBLevel (ray f y n) β is nonempty
  --   have hray_scat : ScatteredFun (rayFun f y n) :=
  --     ray_scattered f hf_scat y n
  --   have hray_level : (CBLevel (rayFun f y n) β).Nonempty := by
  --     -- CB(ray f y n) = β+1 means CBLevel (ray f y n) β ≠ ∅
  --     rw [← hn] at *
  --     exact CBLevel_nonempty_of_rank_gt (rayFun f y n) hray_scat (Order.lt_succ β)
  --   have hray_succ_empty : CBLevel (rayFun f y n) (Order.succ β) = ∅ :=
  --     CBLevel_eq_empty_at_rank (rayFun f y n) hray_scat
  --   have hray_simple : ∃ y' : ℕ → ℕ, ∀ z ∈ CBLevel (rayFun f y n) β,
  --       (rayFun f y n) z = y' :=
  --     ray_simple f hf_scat y n hy
  --   have h_ih : ContinuouslyReduces (MinFun β) (rayFun f y n) :=
  --     ih β (Order.lt_succ β) (by linarith [hα]) hray_scat hray_level
  --       hray_succ_empty hray_simple
  --   -- Now produce (σ, τ) from h_ih satisfying the pointedGluing_lower_bound' conditions
  --   obtain ⟨σ, τ, hσ_cont, hcomm, hτ_cont⟩ := h_ih
  --   -- The domain of rayFun f y n ⊆ U (since we applied rays to f|_U)
  --   -- and f x ∉ closure(range(f ∘ σ)) since range ⊆ ray B y n and y = f x ∉ ray B y n
  --   exact ⟨σ, τ, hσ_cont, hcomm, hτ_cont,
  --     fun z => ray_domain_subset_U f y n U hU hxU z,
  --       -- σ z ∈ U because ray f y n has domain ⊆ U
  --     by
  --       -- f x = y ∉ closure(range(f ∘ σ)) because range(f ∘ σ) ⊆ ray B y n
  --       -- and y is not in the closure of ray B y n (it's clopen, not containing y)
  --       apply ray_disjoint_from_base f y n
  --       -- y ∉ closure(ray B y n) since ray B y n is clopen and y ∉ ray B y n
  --       ⟩
  -- · -- *** Limit case: α is a limit ordinal ***
  --   -- MinFun α = ptgl_n (MinFun αₙ) for (αₙ) cofinal in α
  --   -- The i-th component of MinFun α corresponds to MinFun (cofinal_seq α i)
  --   -- For the given i, find n with CB(ray f y n) > cofinal_seq α i
  --   -- then apply IH
  --   have hcofinal_lt : cofinalSeq α i < α := by
  --     exact cofinalSeq_lt α hlim i
  --   obtain ⟨n, hn⟩ : ∃ n, cofinalSeq α i < CBRank (rayFun f y n) := by
  --     -- regularity + sup = α means (αₙ) is cofinal in α
  --     exact hreg.cofinal_of_sup_eq hsup (cofinalSeq α i) hcofinal_lt
  --   -- Apply IH at cofinalSeq α i:
  --   -- ray f y n has CB rank > cofinalSeq α i, so (CBLevel (ray f y n) (cofinalSeq α i)).Nonempty
  --   have hray_scat : ScatteredFun (rayFun f y n) :=
  --     ray_scattered f hf_scat y n
  --   have hray_level : (CBLevel (rayFun f y n) (cofinalSeq α i)).Nonempty := by
  --     exact CBLevel_nonempty_of_rank_gt (rayFun f y n) hray_scat hn
  --   -- Let β' = CBRank (ray f y n) - 1 so that CB(ray f y n) = β'+1
  --   -- and cofinalSeq α i < β'+1 = CB(ray f y n)
  --   -- The ray is simple:
  --   have hray_simple : ∃ y' : ℕ → ℕ, ∀ z ∈ CBLevel (rayFun f y n) (CBRank (rayFun f y n) - 1),
  --       (rayFun f y n) z = y' :=
  --     ray_simple_at_rank f hf_scat y n
  --   have h_ih : ContinuouslyReduces (MinFun (cofinalSeq α i)) (rayFun f y n) :=
  --     ih (cofinalSeq α i) hcofinal_lt (by linarith [hα]) hray_scat hray_level
  --       (by
  --         -- CBLevel (ray f y n) (succ (cofinalSeq α i)) ⊆ CBLevel (ray f y n) (CBRank (ray f y n)) = ∅
  --         apply Set.eq_empty_of_subset_empty
  --         calc CBLevel (rayFun f y n) (Order.succ (cofinalSeq α i))
  --             ⊆ CBLevel (rayFun f y n) (CBRank (rayFun f y n)) :=
  --               CBLevel_antitone _ (Order.succ_le_of_lt hn)
  --           _ = ∅ := CBLevel_eq_empty_at_rank _ hray_scat)
  --       hray_simple
  --   obtain ⟨σ, τ, hσ_cont, hcomm, hτ_cont⟩ := h_ih
  --   exact ⟨σ, τ, hσ_cont, hcomm, hτ_cont,
  --     fun z => ray_domain_subset_U f y n U hU hxU z,
  --     by apply ray_disjoint_from_base f y n⟩

/--
PROVIDED SOLUTION
-- by induction on α using Ordinal.induction
  -- base case: α = 0, MinFun 0 is the constant function on zerostream, which reduces to any f with nonempty domain
  -- induction step: Assume the statement holds for all β < α. We want to show it holds for α.
  -- Let f : A → ℕ → ℕ be continuous and scattered with (CB level f (succ α)).Nonempty. We want to show MinFun α reduces to f.
  -- Apply decomposition_lemma_baire to f
  -- Apply locally_implies_disjoint_union_baire to get a sequence of clopen sets An such that the restriction of f to each An is simple
  -- Apply cb_rank_of_clopen_union to get that the CB rank of f is the supremum of the CB ranks of f|An
  -- Let β such that β+1 ≤ CBRank f, then there exists An such that CBRank (f|An) ≥ β+1, so for $γCBRank (f|An) ≥ β+2, so (CBLevel (f|An) (β+1)).Nonempty
-/
theorem minFun_is_minimum'
    (α : Ordinal.{0}) (hα : α < omega1) :
      (∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ)
      (hf : Continuous f),
        ScatteredFun f →
        (CBLevel f α).Nonempty → -- this implies CBRank f > α+1
        ContinuouslyReduces (MinFun α) f) := by
  sorry
