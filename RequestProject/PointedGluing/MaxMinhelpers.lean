import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.CBRankHelpers
import RequestProject.PointedGluing.CBLevelOpenRestrict
import RequestProject.PointedGluing.CBRankSimpleHelpers
import RequestProject.PointedGluing.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
## Helper lemmas for MaxFun and MinFun properties
-/

/-
PointedGluingFun with identity functions equals Subtype.val.
-/
lemma PointedGluingFun_id (A : ℕ → Set (ℕ → ℕ)) (x : PointedGluingSet A) :
    PointedGluingFun A A (fun i => id) x = x.val := by
  by_cases hx : x.val = zeroStream <;> simp_all +decide [ PointedGluingFun ];
  have h_eq : x.val = prependZerosOne (firstNonzero x.val) (stripZerosOne (firstNonzero x.val) x.val) := by
    cases x ; simp_all +decide [ PointedGluingSet ];
    unfold PointedGluingSet at *; simp_all +decide [ prependZerosOne, stripZerosOne ] ;
    obtain ⟨ i, x, hx, rfl ⟩ := ‹∃ i, ∃ x ∈ A i, prependZerosOne i x = _›; simp +decide [ firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne ] ;
  rw [ if_pos ];
  · exact h_eq.symm;
  · exact strip_mem_of_pointedGluingSet A x hx

/-
Subtype.val on GluingSet is scattered if each block function is scattered.
-/
lemma gluingSet_subtype_val_scattered
    (F : ℕ → Set (ℕ → ℕ))
    (hF : ∀ i, ScatteredFun (fun (x : F i) => (x.val : ℕ → ℕ))) :
    ScatteredFun (fun (x : GluingSet F) => (x.val : ℕ → ℕ)) := by
  intro S hS;
  obtain ⟨ x, hx ⟩ := hS
  obtain ⟨ i, hi ⟩ := GluingSet_inverse_short F x;
  obtain ⟨ V, hV₁, hV₂, hV₃ ⟩ := hF i { a : F i | ∃ y ∈ S, y.val 0 = i ∧ unprepend y.val = a.val } ⟨ ⟨ unprepend x.val, by aesop ⟩, ⟨ x, hx, by aesop ⟩ ⟩;
  refine' ⟨ { y : GluingSet F | y.val 0 = i ∧ ∃ a ∈ V, unprepend y.val = a.val }, _, _, _ ⟩;
  · obtain ⟨ t, ht₁, ht₂ ⟩ := hV₁;
    refine' ⟨ { y : ℕ → ℕ | y 0 = i ∧ ∃ a ∈ t, unprepend y = a }, _, _ ⟩;
    · simp +decide [ Set.setOf_and, Set.setOf_exists ];
      refine' IsOpen.inter _ _;
      · rw [ isOpen_pi_iff ];
        exact fun f hf => ⟨ { 0 }, fun _ => { i }, by aesop ⟩;
      · exact ht₁.preimage ( show Continuous unprepend from by exact continuous_pi fun _ => continuous_apply _ );
    · simp +decide [ ← ht₂, Set.ext_iff ];
      intro a ha ha' ha''; obtain ⟨ j, hj ⟩ := ha; aesop;
  · obtain ⟨ a, ha₁, ha₂ ⟩ := hV₂;
    exact ⟨ ha₂.choose, ⟨ ha₂.choose_spec.2.1, a, ha₁, ha₂.choose_spec.2.2 ⟩, ha₂.choose_spec.1 ⟩;
  · simp +zetaDelta at *;
    intro a ha ha' ha'' ha''' ha'''' b hb hb' hb'' hb''' hb''''; specialize hV₃ _ ha'' ha''' _ ha ha'''' ha' rfl _ hb'' hb''' _ hb hb'''' hb' rfl;
    exact prepend_unprepend a ▸ prepend_unprepend b ▸ by aesop;

/-
CBLevel of Subtype.val on GluingSet at β = ∅ if each block's CBLevel at β = ∅.
-/
lemma gluingSet_CBLevel_empty
    (F : ℕ → Set (ℕ → ℕ))
    (hF_scat : ScatteredFun (fun (x : GluingSet F) => (x.val : ℕ → ℕ)))
    (β : Ordinal.{0})
    (hF : ∀ i, CBLevel (fun (x : F i) => (x.val : ℕ → ℕ)) β = ∅) :
    CBLevel (fun (x : GluingSet F) => (x.val : ℕ → ℕ)) β = ∅ := by
  set S : ℕ → Set (GluingSet F) := fun n => {x | x.val 0 = n};
  convert CBLevel_clopen_union_empty _ _ _ _ _ _ _;
  exact?;
  exact?;
  convert hF_scat;
  exact fun n => { x : GluingSet F | x.val 0 = n };
  · intro n;
    refine' ⟨ { x : ℕ → ℕ | x 0 = n }, _, _ ⟩;
    · have h_open : IsOpen {x : ℕ → ℕ | x 0 = n} := by
        have h_cont : Continuous (fun x : ℕ → ℕ => x 0) := by
          exact continuous_apply 0
        exact h_cont.isOpen_preimage { n } ( by simp +decide );
      grind +suggestions;
    · rfl;
  · exact fun x => ⟨ _, rfl ⟩;
  · intro n
    have h_iso : CBLevel (fun x : S n => (x.val : ℕ → ℕ)) β = ∅ := by
      specialize hF n;
      contrapose! hF;
      obtain ⟨ x, hx ⟩ := hF;
      use ⟨unprepend x.val.val, by
        have := x.2;
        have := x.1.2;
        obtain ⟨ i, hi ⟩ := this;
        obtain ⟨ j, hj ⟩ := hi.1;
        have := this.symm; simp_all +decide [ prepend ] ;
        subst hj;
        obtain ⟨ y, hy, hy' ⟩ := hi.2; simp_all +decide [ prepend ] ;
        unfold prepend at hy'; aesop;⟩
      generalize_proofs at *;
      induction' β using Ordinal.limitRecOn with β ih generalizing x;
      · unfold CBLevel at *; aesop;
      · simp_all +decide [ CBLevel ];
        intro h;
        refine' hx.2 _;
        obtain ⟨ U, hU₁, hU₂ ⟩ := h;
        refine' ⟨ _, _, _ ⟩;
        exact hx.1;
        exact { y : S n | ⟨ unprepend y.val.val, by
          have := y.1.2;
          obtain ⟨ i, hi ⟩ := this;
          have := y.2; aesop; ⟩ ∈ hU₁ }
        generalize_proofs at *;
        refine' ⟨ _, _, _ ⟩;
        · convert hU₂.1.preimage _ using 1;
          refine' Continuous.subtype_mk _ _;
          exact continuous_unprepend.comp ( continuous_subtype_val.comp continuous_subtype_val );
        · exact hU₂.2.1;
        · intro y hy;
          have := hU₂.2.2 ⟨ unprepend y.val.val, by
            exact? ⟩ ⟨ hy.1, by
            grind +revert ⟩
          generalize_proofs at *;
          simp_all +decide [ funext_iff, unprepend ];
          intro k; induction' k with k ih <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
          exact y.2.trans x.2.symm;
      · rw [ CBLevel_limit ] at hx ⊢;
        · simp_all +decide [ Set.mem_iInter ];
        · assumption;
        · assumption;
    convert h_iso using 1

/-
MaxDom unfolding lemmas
-/
lemma MaxDom_zero : MaxDom 0 = ∅ := by
  unfold MaxDom; rw [Ordinal.limitRecOn_zero]

lemma MaxDom_succ (β : Ordinal.{0}) :
    MaxDom (Order.succ β) = GluingSet (fun _ => PointedGluingSet (fun _ => MaxDom β)) := by
  unfold MaxDom; rw [Ordinal.limitRecOn_succ]

lemma MaxDom_limit (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (_hne : α ≠ 0) :
    MaxDom α = GluingSet (fun n => MaxDom (enumBelow α n)) := by
  unfold MaxDom; rw [Ordinal.limitRecOn_limit _ _ _ _ hlim]

/-
CBLevel_pointedGluing_le: blocks with rank ≤ β have CBLevel β ⊆ {0^ω}
-/
lemma CBLevel_pointedGluing_le
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (β : Ordinal.{0})
    (hβ : ∀ n, CBRank (fun (x : A n) => (f n x : ℕ → ℕ)) ≤ β) :
    CBLevel (fun (x : PointedGluingSet A) => (PointedGluingFun A B f x : ℕ → ℕ)) β ⊆
      {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩} := by
  intro x hx
  by_contra h_contra
  obtain ⟨n, hn⟩ : ∃ n, x.val ∈ blockSet n := by
    have h_block : x.val ∈ ⋃ i, prependZerosOne i '' (A i) := by
      exact Or.resolve_left (x.2) fun h => h_contra <| Subtype.ext <| by aesop
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h_block
    exact ⟨n, by obtain ⟨y, hy, hy'⟩ := hn; exact hy'.symm ▸ prependZerosOne_mem_blockSet n y⟩
  exact CBLevel_block_empty_above_rank A B f hf_scat n β (hβ n) x hn hx

/-
CBLevel singleton implies successor is empty
-/
lemma CBLevel_succ_empty_of_subset_singleton {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (β : Ordinal.{0}) (x : X)
    (h_subset : CBLevel f β ⊆ {x}) :
    CBLevel f (Order.succ β) = ∅ := by
  by_cases h : x ∈ CBLevel f β <;> simp_all +decide [ CBLevel ];
  · simp +decide [ Set.ext_iff, isolatedLocus ];
    intro y hy; use Set.univ; simp [hy];
    intro z hz;
    rw [ h_subset z ( by
      convert hz using 1;
      ext; simp [isolatedLocus] ), h_subset y ( by
      convert hy using 1;
      ext; simp [isolatedLocus] ) ];
  · grind

/-
Subtype.val on PointedGluingSet is scattered if each block is scattered.
-/
lemma pointedGluingSet_subtype_val_scattered
    (A : ℕ → Set (ℕ → ℕ))
    (hA : ∀ i, ScatteredFun (fun (x : A i) => (x.val : ℕ → ℕ))) :
    ScatteredFun (fun (x : PointedGluingSet A) => (x.val : ℕ → ℕ)) := by
  convert pointedGluing_scattered A A ( fun i => id ) ( fun i => by simpa using hA i ) using 1;
  exact funext fun x => Eq.symm ( PointedGluingFun_id A x )

/-
CBLevel of Subtype.val on PointedGluingSet empties above the CB-ranks of the blocks.
-/
lemma pointedGluingSet_subtype_val_CBLevel_empty
    (A : ℕ → Set (ℕ → ℕ))
    (hA_scat : ∀ i, ScatteredFun (fun (x : A i) => (x.val : ℕ → ℕ)))
    (γ : Ordinal.{0})
    (hA_cb : ∀ i, CBLevel (fun (x : A i) => (x.val : ℕ → ℕ)) γ = ∅)
    (β : Ordinal.{0}) (hβ : Order.succ γ ≤ β) :
    CBLevel (fun (x : PointedGluingSet A) => (x.val : ℕ → ℕ)) β = ∅ := by
  have := @CBLevel_pointedGluing_le A A ( fun i => id ) ?_ γ ?_ <;> simp_all +decide;
  · have hCBLevel_succ_empty : CBLevel (fun (x : PointedGluingSet A) => (x.val : ℕ → ℕ)) (Order.succ γ) = ∅ := by
      apply CBLevel_succ_empty_of_subset_singleton;
      swap;
      exact ⟨ zeroStream, zeroStream_mem_pointedGluingSet A ⟩;
      intro x hx; specialize this x.val x.property; simp_all +decide [ PointedGluingFun_id ] ;
      exact Subtype.ext this;
    exact Set.eq_empty_of_forall_notMem fun x hx => by have := CBLevel_antitone ( fun x : PointedGluingSet A => ( x.val : ℕ → ℕ ) ) ( Order.succ_le_of_lt hβ ); aesop;
  · exact fun n => CBRank_le_of_CBLevel_empty _ _ ( hA_cb n )

/-
MinDom unfolding lemmas
-/
lemma MinDom_zero : MinDom 0 = PointedGluingSet (fun _ => ∅) := by
  unfold MinDom; rw [Ordinal.limitRecOn_zero]

lemma MinDom_succ (β : Ordinal.{0}) :
    MinDom (Order.succ β) = PointedGluingSet (fun _ => MinDom β) := by
  unfold MinDom; rw [Ordinal.limitRecOn_succ]

lemma MinDom_limit (α : Ordinal.{0}) (hlim : Order.IsSuccLimit α) (_hne : α ≠ 0) :
    MinDom α = PointedGluingSet (fun n => MinDom (cofinalSeq α n)) := by
  unfold MinDom; rw [Ordinal.limitRecOn_limit _ _ _ _ hlim]

/-
MaxFun α is scattered with CB-rank ≤ α (in fact equal)
-/
lemma maxfun_is_scatter_leq_α (α : Ordinal.{0}) (hα : α < omega1) : ScatteredFun (MaxFun α) ∧
    (∀ β : Ordinal.{0}, α < β → CBLevel (MaxFun α) β = ∅) := by
  have h_ind : ∀ α : Ordinal.{0}, α ≤ omega1 → (∀ β, β < α → ScatteredFun (MaxFun β) ∧ ∀ γ, β < γ → CBLevel (MaxFun β) γ = ∅) → ScatteredFun (MaxFun α) ∧ ∀ β, α < β → CBLevel (MaxFun α) β = ∅ := by
    intro α hα ih;
    by_cases hα_zero : α = 0;
    · grind +suggestions;
    · by_cases hα_succ : ∃ β, α = Order.succ β;
      · obtain ⟨β, rfl⟩ := hα_succ;
        have h_succ : ScatteredFun (fun (x : GluingSet (fun _ => PointedGluingSet (fun _ => MaxDom β))) => (x.val : ℕ → ℕ)) := by
          apply gluingSet_subtype_val_scattered;
          intro i;
          apply pointedGluingSet_subtype_val_scattered;
          exact fun _ => ih β ( Order.lt_succ β ) |>.1;
        have h_succ_cb : ∀ γ, Order.succ β < γ → CBLevel (fun (x : GluingSet (fun _ => PointedGluingSet (fun _ => MaxDom β))) => (x.val : ℕ → ℕ)) γ = ∅ := by
          intros γ hγ;
          apply gluingSet_CBLevel_empty;
          · exact h_succ;
          · intros i
            apply pointedGluingSet_subtype_val_CBLevel_empty;
            exact fun _ => ih β ( Order.lt_succ β ) |>.1;
            exact fun _ => ih β ( Order.lt_succ β ) |>.2 _ ( Order.lt_succ β );
            exact?;
        unfold MaxFun;
        rw [ MaxDom_succ ] ; aesop;
      · have hα_limit : Order.IsSuccLimit α := by
          constructor;
          · exact?;
          · intro β hβ;
            exact hα_succ ⟨ β, hβ.succ_eq.symm ⟩;
        have h_max_fun_limit : ScatteredFun (fun (x : GluingSet (fun n => MaxDom (enumBelow α n))) => (x.val : ℕ → ℕ)) := by
          apply gluingSet_subtype_val_scattered;
          intro n
          apply (ih (enumBelow α n) (by
          exact?)).left;
        have h_max_fun_limit : ∀ β, α < β → CBLevel (fun (x : GluingSet (fun n => MaxDom (enumBelow α n))) => (x.val : ℕ → ℕ)) β = ∅ := by
          intros β hβ
          apply gluingSet_CBLevel_empty;
          · exact h_max_fun_limit;
          · intro i
            have hβ_gt_enum : enumBelow α i < α := by
              exact?
            have hβ_gt_enum' : enumBelow α i < β := by
              exact lt_trans hβ_gt_enum hβ
            exact ih (enumBelow α i) hβ_gt_enum |>.2 β hβ_gt_enum';
        unfold MaxFun;
        rw [ MaxDom_limit α hα_limit hα_zero ] ; aesop;
  have h_ind : ∀ α : Ordinal.{0}, α ≤ omega1 → ScatteredFun (MaxFun α) ∧ ∀ β, α < β → CBLevel (MaxFun α) β = ∅ := by
    intro α hα
    induction' α using Ordinal.induction with α ih;
    exact h_ind α hα fun β hβ => ih β hβ <| hβ.le.trans hα;
  exact h_ind α hα.le

/-
MinFun α is scattered with CB-rank ≤ α+1 (in fact equal)
-/
lemma minfun_is_scatter_leq_succ_α (α : Ordinal.{0}) (hα : α < omega1) : ScatteredFun (MinFun α) ∧
    (∀ β : Ordinal.{0}, Order.succ α < β → CBLevel (MinFun α) β = ∅) := by
  induction' α using Ordinal.limitRecOn with α ih;
  · constructor;
    · unfold MinDom;
      simp +decide [ PointedGluingSet ];
      intro S hS; use Set.univ; aesop;
    · intro β hβ
      have h_singleton : CBLevel (MinFun 0) (Order.succ 0) = ∅ := by
        unfold CBLevel;
        simp +decide [ Ordinal.limitRecOn ];
        unfold isolatedLocus;
        simp +decide [ Set.ext_iff ];
        intro a ha
        use Set.univ
        simp [MinFun];
        unfold MinDom at *; simp_all +decide [ PointedGluingSet ] ;
      have h_singleton : ∀ β, Order.succ 0 < β → CBLevel (MinFun 0) β = ∅ := by
        intros β hβ;
        have h_singleton : ∀ β, Order.succ 0 < β → CBLevel (MinFun 0) β ⊆ CBLevel (MinFun 0) (Order.succ 0) := by
          intros β hβ;
          apply CBLevel_antitone;
          exact le_of_lt hβ;
        exact Set.eq_empty_of_forall_notMem fun x hx => by have := h_singleton β hβ hx; aesop;
      exact h_singleton β hβ;
  · constructor;
    · convert pointedGluingSet_subtype_val_scattered ( fun _ => MinDom α ) _ using 1;
      · rw [ MinDom_succ ];
      · congr! 1;
        ext; simp [MinDom_succ];
      · unfold MinFun;
        congr! 1;
        ext; simp [MinDom_succ];
      · exact fun _ => ih ( lt_trans ( Order.lt_succ α ) hα ) |>.1;
    · intro β hβ;
      convert pointedGluingSet_subtype_val_CBLevel_empty ( fun _ => MinDom α ) _ ( Order.succ ( Order.succ α ) ) _ β _;
      · rw [ show MinFun ( Order.succ α ) = fun x : MinDom ( Order.succ α ) => ( x.val : ℕ → ℕ ) from ?_ ];
        · rw [ MinDom_succ ];
        · exact?;
      · exact fun _ => ih ( lt_of_le_of_lt ( Order.le_succ _ ) hα ) |>.1;
      · exact fun _ => ih ( lt_of_le_of_lt ( Order.le_succ _ ) hα ) |>.2 _ ( Order.lt_succ _ );
      · exact Order.succ_le_of_lt hβ;
  · apply And.intro;
    · rename_i α hα ih;
      have h_minfun_scattered : ∀ n, ScatteredFun (fun (x : MinDom (cofinalSeq α n)) => (x.val : ℕ → ℕ)) := by
        intro n
        apply (ih (cofinalSeq α n) (by
        exact cofinalSeq_lt α ‹_› ( by aesop ) n) (by
        exact lt_of_lt_of_le ( cofinalSeq_lt α ‹_› ( by aesop ) n ) hα.le)).left;
      convert pointedGluingSet_subtype_val_scattered _ h_minfun_scattered using 1;
      · rw [ MinDom_limit α ‹_› ( by aesop ) ];
      · congr! 1;
        ext; simp [MinDom_limit α ‹_› (by
        aesop)];
      · unfold MinFun;
        congr! 1;
        ext; simp [MinDom_limit α ‹_› (by
        aesop)];
    · rename_i o ho ih;
      -- Since each block is MinDom (cofinalSeq o n), and by the induction hypothesis, each of these blocks has CBLevel at β empty for β > Order.succ (cofinalSeq o n).
      have h_block_empty : ∀ n, CBLevel (fun (x : MinDom (cofinalSeq o n)) => (x.val : ℕ → ℕ)) (Order.succ o) = ∅ := by
        intro n
        have h_block_empty : cofinalSeq o n < o := by
          apply cofinalSeq_lt o ho (Order.IsSuccLimit.ne_bot ho) n;
        have := ih ( cofinalSeq o n ) h_block_empty ( lt_trans h_block_empty hα );
        exact this.2 _ ( Order.succ_lt_succ h_block_empty );
      intro β hβ
      have h_pointedGluing_empty : CBLevel (fun (x : PointedGluingSet (fun n => MinDom (cofinalSeq o n))) => (x.val : ℕ → ℕ)) β = ∅ := by
        apply pointedGluingSet_subtype_val_CBLevel_empty;
        any_goals tauto;
        · intro n
          have h_ind : cofinalSeq o n < o := by
            apply cofinalSeq_lt o ho (Order.IsSuccLimit.ne_bot ho) n
          have h_ind' : cofinalSeq o n < omega1 := by
            exact lt_trans h_ind hα
          exact (ih (cofinalSeq o n) h_ind h_ind').left;
        · exact?;
      convert h_pointedGluing_empty using 1;
      unfold MinFun;
      rw [ MinDom_limit o ho ( by aesop ) ]

lemma MaxFun_monotone (α β: Ordinal.{0})
    (hα : α < omega1) (hβ : β < omega1)
    (hl: α ≤ β):
    ContinuouslyReduces (MaxFun α) (MaxFun β) := by
  -- by induction on beta, we show that if α ≤ β then (MaxFun α) ≤ (MaxFun β)
  -- beta = 0 implies α =0 and so trivial
  -- \beta= \gamma+1 successor, we show that (MaxFun γ) ≤ (MaxFun β)
  -- since (MaxFun β) is the gluing of copies pointedgluing of MaxFun γ,
  -- we can choose σ to be x ↦ prepend 0 (prepend 1 x) and tau y↦ unprepend (unprepend y)
  -- by induction hypothesis for every α ≤ γ we have
  -- (MaxFun α) ≤ (MaxFun γ) so we conclude by transitivity
  -- β limit, let α<β. By definition of (MaxFun β) is the gluing of MaxFun β_n
  -- for a sequence β_n cofinal in β. So there exists n such that
  -- α≤ β_n and by induction hypothesis  (MaxFun α) ≤ (MaxFun β_n)
  -- now clearly  (MaxFun β_n) ≤ (MaxFun β) by σ : x↦ prepend n x and τ: y↦unprepend y
  sorry

lemma MinFun_monotone (α β: Ordinal.{0})
    (hα : α < omega1) (hβ : β < omega1)
    (hl: α ≤ β):
    ContinuouslyReduces (MinFun α) (MinFun β) := by
  -- by induction on beta, we show that if α ≤ β then (MinFun α) ≤ (MinFun β)
  -- beta = 0 implies α =0 and so trivial
  -- \beta= \gamma+1 successor, we show that (MinFun γ) ≤ (MinFun β)
  -- since (MinFun β) is the pointedgluing of copies of MinFun γ,
  -- we can choose σ to be x ↦ prepend 1 x and tau y↦ unprepend y
  -- by induction hypothesis for every α ≤ γ we have
  -- (MinFun α) ≤ (MinFun γ) so we conclude by transitivity
  -- β limit, let α<β. By definition of (MinFun β) is the pointedgluing of MinFun β_n
  -- for a sequence β_n cofinal in β. So there exists n such that
  -- α≤ β_n and by induction hypothesis  (MinFun α) ≤ (MinFun β_n)
  -- now clearly  (MinFun β_n) ≤ (MinFun β) by σ : x↦ prepend 1 x and τ: y↦unprepend y
  sorry
end
