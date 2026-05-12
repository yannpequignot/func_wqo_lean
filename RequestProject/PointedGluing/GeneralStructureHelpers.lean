import RequestProject.PointedGluing.MinFun
import Mathlib

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
# Helper lemmas for the General Structure Theorem
-/

/-- For non-zeroStream x in PointedGluingSet,
x = prependZerosOne (firstNonzero x) (stripZerosOne (firstNonzero x) x) -/
lemma pgs_reconstruct {A : ℕ → Set (ℕ → ℕ)}
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    x.val = prependZerosOne (firstNonzero x.val) (stripZerosOne (firstNonzero x.val) x.val) := by
  have : ∃ j, ∃ a ∈ A j, (↑x : ℕ → ℕ) = prependZerosOne j a := by
    rcases x with ⟨v, hv⟩; simp [PointedGluingSet] at hv
    rcases hv with rfl | ⟨j, a, ha, rfl⟩
    · exact absurd rfl hx
    · exact ⟨j, a, ha, rfl⟩
  obtain ⟨j, a, _, ha⟩ := this
  rw [ha, firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]

/-- PointedGluingFun maps into PointedGluingSet -/
lemma pgl_fun_mem (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) :
    PointedGluingFun A B f x ∈ PointedGluingSet B := by
  unfold PointedGluingFun; split_ifs with h1
  · exact Or.inl rfl
  · simp only []; split_ifs with h2
    · exact Or.inr (Set.mem_iUnion.mpr ⟨_, _, (f _ ⟨_, h2⟩).prop, rfl⟩)
    · exact absurd (strip_mem_of_pointedGluingSet A x h1) h2

/-
Helper: the range of σ' consists of zeroStream and prependZerosOne i (σ a).val.
-/
private lemma pgl_range_structure (A B : Set (ℕ → ℕ)) (σ : A → B) :
    let σ' := fun x : PointedGluingSet (fun _ => A) =>
      (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
        pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))
    ∀ z ∈ Set.range (Subtype.val ∘ σ'), z ≠ zeroStream →
      ∃ i : ℕ, ∃ a : A,
        z = prependZerosOne i ((σ a).val) ∧
        firstNonzero z = i ∧
        stripZerosOne i z = (σ a).val := by
  unfold PointedGluingFun;
  grind +suggestions

/-
Helper: ContinuousWithinAt at zeroStream for the τ' map.
-/
private lemma pgl_tau_cwat_zero (A B : Set (ℕ → ℕ))
    (σ : A → B) (hσ : Continuous σ)
    (τ : (ℕ → ℕ) → (ℕ → ℕ)) (hτ : ContinuousOn τ (Set.range (Subtype.val ∘ σ)))
    (heq : ∀ (a : A), a.val = τ ((σ a).val)) :
    let τ' := fun y => if y = zeroStream then zeroStream
      else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y))
    let R := Set.range (Subtype.val ∘
      (fun x : PointedGluingSet (fun _ => A) =>
        (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
          pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))))
    ContinuousWithinAt τ' R zeroStream := by
  -- Apply the lemma continuousWithinAt_tau_at_zeroStream with the given parameters.
  apply continuousWithinAt_tau_at_zeroStream;
  exact?;
  rotate_right;
  use fun n => { n };
  · simp +contextual [ Set.disjoint_left ];
  · simp +zetaDelta at *;
    intro z x hx hz hz' k hk; rw [ if_neg hz' ] ; exact prependZerosOne_head_eq_zero _ _ _ hk;

/-
Helper: ContinuousWithinAt at non-zeroStream points for the τ' map.
-/
private lemma pgl_tau_cwat_block (A B : Set (ℕ → ℕ))
    (σ : A → B) (hσ : Continuous σ)
    (τ : (ℕ → ℕ) → (ℕ → ℕ)) (hτ : ContinuousOn τ (Set.range (Subtype.val ∘ σ)))
    (heq : ∀ (a : A), a.val = τ ((σ a).val)) :
    let τ' := fun y => if y = zeroStream then zeroStream
      else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y))
    let R := Set.range (Subtype.val ∘
      (fun x : PointedGluingSet (fun _ => A) =>
        (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
          pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))))
    ∀ z₀ ∈ R, z₀ ≠ zeroStream → ContinuousWithinAt τ' R z₀ := by
  intro τ' R z₀ hz₀ hz₀_ne;
  -- Let $i₀ = firstNonzero z₀$.
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, firstNonzero z₀ = i₀ ∧ (∀ k < i₀, z₀ k = 0) ∧ z₀ i₀ ≠ 0 := by
    unfold firstNonzero; simp +decide [ hz₀_ne ] ;
    split_ifs with h <;> simp_all +singlePass [ funext_iff ];
    · exact Nat.find_spec h;
    · exact hz₀_ne.elim fun n hn => hn <| by unfold zeroStream; simp +decide ;
  -- On R ∩ U, every z has firstNonzero z = i₀ (by firstNonzero_eq_of_block), so:
  have h_block : ∀ z ∈ R, z ∈ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0} → firstNonzero z = i₀ := by
    intros z hz hz_block;
    unfold firstNonzero at *;
    split_ifs at * <;> simp_all +singlePass [ Nat.find_eq_iff ];
  -- Let $g = \text{prependZerosOne } i₀ \circ \tau \circ \text{stripZerosOne } i₀$.
  set g : (ℕ → ℕ) → (ℕ → ℕ) := fun y => prependZerosOne i₀ (τ (stripZerosOne i₀ y));
  -- We need to show that $g$ is continuous on $R \cap U$.
  have h_g_cont : ContinuousOn g (R ∩ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0}) := by
    refine' ContinuousOn.comp ( show ContinuousOn ( fun y => prependZerosOne i₀ y ) ( Set.range ( fun y => τ ( stripZerosOne i₀ y ) ) ) from _ ) _ _;
    · exact Continuous.continuousOn ( continuous_prependZerosOne _ );
    · refine' hτ.comp _ _;
      · exact Continuous.continuousOn ( continuous_stripZerosOne i₀ );
      · intro x hx; obtain ⟨ y, rfl ⟩ := hx.1; simp +decide [ PointedGluingFun ] at *;
        split_ifs at hx <;> simp_all +singlePass [ firstNonzero_eq_of_block ];
        · exact False.elim <| hx.2.2 <| by rfl;
        · grind +suggestions;
        · exact False.elim <| hx.2.2 <| by simp +decide [ zeroStream ] ;
    · exact fun x hx => Set.mem_range_self _;
  have h_g_eq : ∀ z ∈ R, z ∈ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0} → τ' z = g z := by
    simp +zetaDelta at *;
    intro z x hx hz hz' hz''; rw [ if_neg ( by rintro rfl; exact hz'' ( by simp +decide [ zeroStream ] ) ) ] ; rw [ h_block z x hx hz hz' hz'' ] ;
  have h_g_eq : ContinuousWithinAt τ' (R ∩ {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0}) z₀ := by
    exact ContinuousOn.continuousWithinAt ( h_g_cont.congr fun x hx => h_g_eq x hx.1 hx.2 ▸ rfl ) ( by aesop );
  rw [ ContinuousWithinAt ] at *;
  rw [ nhdsWithin_inter ] at h_g_eq;
  convert h_g_eq using 1;
  rw [ inf_eq_left.mpr ];
  rw [ nhdsWithin_le_iff ];
  rw [ mem_nhdsWithin_iff_exists_mem_nhds_inter ];
  use {x | (∀ k < i₀, x k = 0) ∧ x i₀ ≠ 0};
  exact ⟨ isOpen_block i₀ |> IsOpen.mem_nhds <| by tauto, fun x hx => hx.1 ⟩

/-- ContinuousOn for the τ' in pgl_functorial_val. -/
lemma pgl_tau_continuousOn (A B : Set (ℕ → ℕ))
    (σ : A → B) (hσ : Continuous σ)
    (τ : (ℕ → ℕ) → (ℕ → ℕ)) (hτ : ContinuousOn τ (Set.range (Subtype.val ∘ σ)))
    (heq : ∀ (a : A), a.val = τ ((σ a).val)) :
    ContinuousOn
      (fun y => if y = zeroStream then zeroStream
        else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y)))
      (Set.range (Subtype.val ∘
        (fun x : PointedGluingSet (fun _ => A) =>
          (⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
            pgl_fun_mem _ _ _ x⟩ : PointedGluingSet (fun _ => B))))) := by
  intro z hz
  by_cases hz0 : z = zeroStream
  · subst hz0; exact pgl_tau_cwat_zero A B σ hσ τ hτ heq
  · exact pgl_tau_cwat_block A B σ hσ τ hτ heq z hz hz0

/-- Functoriality of PointedGluing for constant sequences. -/
lemma pgl_functorial_val (A B : Set (ℕ → ℕ))
    (h : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (Subtype.val : B → ℕ → ℕ)) :
    ContinuouslyReduces
      (Subtype.val : PointedGluingSet (fun _ => A) → ℕ → ℕ)
      (Subtype.val : PointedGluingSet (fun _ => B) → ℕ → ℕ) := by
  obtain ⟨σ, hσ, τ, hτ, heq⟩ := h
  refine ⟨fun x => ⟨PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x,
    pgl_fun_mem _ _ _ x⟩, ?_, ?_⟩
  · exact pointedGluingFun_preserves_continuity _ _ _ (fun _ => hσ)
  · refine ⟨fun y => if y = zeroStream then zeroStream
      else prependZerosOne (firstNonzero y) (τ (stripZerosOne (firstNonzero y) y)),
      pgl_tau_continuousOn A B σ hσ τ hτ heq, ?_⟩
    intro x
    show x.val = _
    simp only []
    by_cases hx : x.val = zeroStream
    · have : PointedGluingFun (fun _ => A) (fun _ => B) (fun _ => σ) x = zeroStream := by
        unfold PointedGluingFun; simp [hx]
      rw [this, if_pos rfl, hx]
    · have hmem := strip_mem_of_pointedGluingSet (fun _ => A) x hx
      rw [pointedGluingFun_eq_on_block (fun _ => A) (fun _ => B) (fun _ => σ) x hx]
      rw [if_neg (prependZerosOne_ne_zeroStream _ _)]
      rw [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne]
      conv_lhs => rw [pgs_reconstruct x hx]
      congr 1
      exact heq ⟨_, hmem⟩

/-- The GluingSet of copies of PointedGluingSet reduces to PointedGluingSet of PointedGluingSet.
This is ω · pgl(X) ≤ pgl(pgl(X)). -/
lemma omega_pgl_le_pgl_pgl (A : Set (ℕ → ℕ)) :
    ContinuouslyReduces
      (Subtype.val : GluingSet (fun _ => PointedGluingSet (fun _ => A)) → ℕ → ℕ)
      (Subtype.val : PointedGluingSet (fun _ => PointedGluingSet (fun _ => A)) → ℕ → ℕ) := by
  convert gluing_le_pointedGluing (fun _ => PointedGluingSet (fun _ => A))
    (fun _ => PointedGluingSet (fun _ => A)) (fun _ => id)
  · ext; simp [GluingFunVal]
    rename_i k; cases k <;> simp +decide [prepend, unprepend]
  · exact funext fun x => Eq.symm (PointedGluingFun_id _ _)

/-- For limit η, adding a finite natural number m stays below η. -/
lemma limit_add_nat_lt (η : Ordinal.{0}) (hlim : Order.IsSuccLimit η) (hne : η ≠ 0)
    (α : Ordinal.{0}) (hα : α < η) (m : ℕ) :
    α + ↑m < η := by
  induction' m with m ih
  · simpa using hα
  · convert hlim.succ_lt ih using 1
    simp +decide [add_assoc, Ordinal.add_succ]

/-- Every ordinal can be decomposed as α' + m where α' is limit or 0 and m ∈ ℕ. -/
lemma ordinal_limit_nat_decomposition (α : Ordinal.{0}) :
    ∃ (α' : Ordinal.{0}) (m : ℕ),
      (Order.IsSuccLimit α' ∨ α' = 0) ∧ α = α' + ↑m := by
  by_contra! h_contra
  induction' α using Ordinal.induction with α ih
  by_cases hα : Order.IsSuccLimit α ∨ α = 0
  · exact h_contra α 0 hα (by simp +decide)
  · obtain ⟨β, rfl⟩ : ∃ β, α = Order.succ β := by
      simp_all +decide [Order.IsSuccLimit]
      simp_all +decide [Order.IsSuccPrelimit]
      exact Exists.elim (hα.1 hα.2) fun x hx => ⟨x, hx.succ_eq.symm⟩
    specialize ih β (Order.lt_succ β) ; simp_all +decide [not_or]
    obtain ⟨α', hα', m, hm⟩ := ih; specialize h_contra α' (m + 1) ; simp_all +decide [add_assoc]
    exact h_contra (by rw [Ordinal.add_succ])

/-- For every ordinal β < η (limit), there exists n such that cofinalSeq η n ≥ β. -/
lemma cofinalSeq_eventually_ge (η : Ordinal.{0}) (hη : η < omega1)
    (hlim : Order.IsSuccLimit η) (hne : η ≠ 0)
    (β : Ordinal.{0}) (hβ : β < η) :
    ∃ n : ℕ, β ≤ cofinalSeq η n := by
  have h_surj : Function.Surjective (fun n => ⟨cofinalSeq η n, cofinalSeq_lt η hlim hne n⟩ : ℕ → Iio η) := by
    convert enumBelow_surj η hη hne using 1
    unfold cofinalSeq; aesop
  cases' h_surj ⟨β, hβ⟩ with n hn ; use n ; aesop

/-
Successor step for MaxFun_le_MinFun:
If MaxFun(α) ≤ MinFun(β), then MaxFun(succ α) ≤ MinFun(succ (succ β)).
-/
lemma MaxFun_le_MinFun_succ (α β : Ordinal.{0})
    (h : ContinuouslyReduces (MaxFun α) (MinFun β)) :
    ContinuouslyReduces (MaxFun (Order.succ α)) (MinFun (Order.succ (Order.succ β))) := by
  have h_maxFun_succ : MaxFun (Order.succ α) = Subtype.val := by
    -- By definition of MaxFun, we know that MaxFun (Order.succ α) is the subtype val.
    funext x; simp [MaxFun];
  convert h_maxFun_succ using 1;
  constructor <;> intro h;
  · lia;
  · convert omega_pgl_le_pgl_pgl ( MaxDom α ) |> fun h => h.trans ( pgl_functorial_val _ _ <| pgl_functorial_val _ _ ‹MaxFun α ≤ MinFun β› ) using 1;
    all_goals congr! 1;
    all_goals norm_num [ MaxFun, MinFun, MaxDom_succ, MinDom_succ ];
    · grind;
    · rfl;
    · congr! 1;
      ext; simp [MaxDom_succ];
    · congr! 1;
      ext; simp [MinDom_succ]

/-
Membership: unprepend x.val ∈ A (x.val 0) for x ∈ GluingSet A.
-/
private lemma unprepend_mem_of_gluingSet (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) :
    unprepend x.val ∈ A (x.val 0) := by
  exact GluingSet_inverse_short A x |> fun ⟨ i, hi1, hi2 ⟩ => hi1 ▸ hi2

/-
σ' is continuous: on each block, it's a composition of continuous functions.
-/
private lemma gluing_to_pgluing_sigma_cont
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ)
    (σ_n : ∀ n, A n → B (p n))
    (hσc : ∀ n, Continuous (σ_n n)) :
    Continuous (fun x : GluingSet A =>
      (⟨prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val,
        unprepend_mem_of_gluingSet A x⟩ : B (p (x.val 0))).val),
       prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩ : PointedGluingSet B)) := by
  refine' Continuous.subtype_mk _ _;
  have h_unprepend_cont : Continuous (fun x : GluingSet A => unprepend x.val) := by
    exact continuous_unprepend.comp continuous_subtype_val;
  have h_cont : ∀ n, Continuous (fun x : {x : GluingSet A | x.val 0 = n} => prependZerosOne (p n) ((σ_n n ⟨unprepend x.val, by
    convert unprepend_mem_of_gluingSet A x ; aesop⟩).val)) := by
    intro n
    have h_cont : Continuous (fun x : {x : GluingSet A | x.val 0 = n} => (σ_n n ⟨unprepend x.val, by
      convert unprepend_mem_of_gluingSet A x ; aesop⟩).val) := by
      exact Continuous.comp ( continuous_subtype_val ) ( hσc n |> Continuous.comp <| Continuous.subtype_mk ( h_unprepend_cont.comp <| continuous_subtype_val ) _ )
    generalize_proofs at *;
    exact Continuous.comp ( show Continuous ( fun x : ℕ → ℕ => prependZerosOne ( p n ) x ) from continuous_prependZerosOne _ ) h_cont
  generalize_proofs at *;
  have h_cont : ∀ n, ContinuousOn (fun x : GluingSet A => prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val, by
    solve_by_elim⟩).val)) {x : GluingSet A | x.val 0 = n} := by
    intro n
    generalize_proofs at *;
    rw [ continuousOn_iff_continuous_restrict ];
    convert h_cont n using 1;
    grind
  generalize_proofs at *;
  refine' continuous_iff_continuousAt.mpr fun x => _;
  have := h_cont ( x.val 0 );
  convert this.continuousAt _ using 1;
  rw [ mem_nhds_iff ];
  refine' ⟨ { y : GluingSet A | y.val 0 = x.val 0 }, _, _, _ ⟩ <;> norm_num;
  refine' ⟨ { y : ℕ → ℕ | y 0 = x.val 0 }, _, _ ⟩;
  · rw [ isOpen_pi_iff ];
    exact fun f hf => ⟨ { 0 }, fun _ => { y | y = x.val 0 }, by aesop ⟩;
  · rfl

/-
Elements of the range in block p(n₀) come from σ_n₀.
-/
private lemma gluing_sigma_range_block
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ) (hp : Injective p)
    (σ_n : ∀ n, A n → B (p n))
    (n₀ : ℕ) :
    let σ' := fun x : GluingSet A =>
      (⟨prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val,
        unprepend_mem_of_gluingSet A x⟩ : B (p (x.val 0))).val),
       prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩ : PointedGluingSet B)
    ∀ y ∈ Set.range (Subtype.val ∘ σ') ∩
        {y : ℕ → ℕ | (∀ k < p n₀, y k = 0) ∧ y (p n₀) ≠ 0},
      stripZerosOne (p n₀) y ∈ Set.range (Subtype.val ∘ σ_n n₀) := by
  intro σ' y hy
  obtain ⟨x, hx⟩ := hy.left
  simp only [comp_def] at hx;
  have h_firstNonzero_eq : firstNonzero y = p n₀ := by
    apply firstNonzero_eq_of_block;
    exact hy.2;
  grind +suggestions

/-
τ' is ContinuousOn the range.
-/
private lemma gluing_to_pgluing_tau_cont
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ) (hp : Injective p)
    (σ_n : ∀ n, A n → B (p n))
    (hσc : ∀ n, Continuous (σ_n n))
    (τ_n : ∀ n, (ℕ → ℕ) → (ℕ → ℕ))
    (hτc : ∀ n, ContinuousOn (τ_n n) (Set.range (Subtype.val ∘ σ_n n)))
    (heq : ∀ n (a : A n), a.val = τ_n n ((σ_n n a).val)) :
    let σ' := fun x : GluingSet A =>
      (⟨prependZerosOne (p (x.val 0)) ((σ_n (x.val 0) ⟨unprepend x.val,
        unprepend_mem_of_gluingSet A x⟩ : B (p (x.val 0))).val),
       prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩ : PointedGluingSet B)
    ContinuousOn
      (fun y => prepend (Function.invFun p (firstNonzero y)) (τ_n (Function.invFun p (firstNonzero y)) (stripZerosOne (firstNonzero y) y)))
      (Set.range (Subtype.val ∘ σ')) := by
  intro x;
  refine' fun y hy => continuousWithinAt_tau_at_block _ _ _;
  · exact hy;
  · obtain ⟨ x, rfl ⟩ := hy;
    exact prependZerosOne_ne_zeroStream _ _;
  · refine' ⟨ { z | ( ∀ k < firstNonzero y, z k = 0 ) ∧ z ( firstNonzero y ) ≠ 0 }, isOpen_block _, _, _ ⟩;
    · obtain ⟨ z, rfl ⟩ := hy;
      unfold firstNonzero; simp +decide [ prependZerosOne_head_eq_zero, prependZerosOne_at_i ] ;
      split_ifs with h;
      · exact ⟨ fun k hk => by simpa using Nat.find_min ( show ∃ k, ¬ ( x z : ℕ → ℕ ) k = 0 from h ) hk, Nat.find_spec ( show ∃ k, ¬ ( x z : ℕ → ℕ ) k = 0 from h ) ⟩;
      · simp +zetaDelta at *;
        exact absurd ( h ( p ( z.val 0 ) ) ) ( by simp +decide [ prependZerosOne ] );
    · refine' ⟨ _, _, fun z hz => rfl ⟩;
      refine' ContinuousOn.congr _ _;
      use fun z => prepend ( invFun p ( firstNonzero y ) ) ( τ_n ( invFun p ( firstNonzero y ) ) ( stripZerosOne ( firstNonzero y ) z ) );
      · refine' ContinuousOn.comp ( continuous_prepend _ |> Continuous.continuousOn ) _ _;
        exact Set.univ;
        · refine' ContinuousOn.comp ( hτc _ ) _ _;
          · exact Continuous.continuousOn ( continuous_stripZerosOne _ );
          · intro z hz;
            convert gluing_sigma_range_block A B p hp σ_n ( invFun p ( firstNonzero y ) ) z _ using 1;
            · rw [ invFun_eq ( show ∃ n, p n = firstNonzero y from _ ) ];
              grind +suggestions;
            · rw [ invFun_eq ( show ∃ n, p n = firstNonzero y from _ ) ];
              · exact hz;
              · grind +suggestions;
        · exact fun _ _ => Set.mem_univ _;
      · intro z hz;
        have h_firstNonzero : firstNonzero z = firstNonzero y := by
          apply firstNonzero_eq_of_block;
          exact hz.2;
        grind +splitImp

/-- Gluing of reductions with an injection. -/
lemma gluing_reduces_to_pgluing_via_injection
    (A B : ℕ → Set (ℕ → ℕ))
    (p : ℕ → ℕ) (hp : Injective p)
    (h : ∀ n, ContinuouslyReduces
      (Subtype.val : A n → ℕ → ℕ) (Subtype.val : B (p n) → ℕ → ℕ)) :
    ContinuouslyReduces
      (Subtype.val : GluingSet A → ℕ → ℕ)
      (Subtype.val : PointedGluingSet B → ℕ → ℕ) := by
  choose σ_n hσc τ_n hτc heq using h
  refine ⟨fun x => ⟨prependZerosOne (p (x.val 0))
      ((σ_n (x.val 0) ⟨unprepend x.val, unprepend_mem_of_gluingSet A x⟩ :
        B (p (x.val 0))).val),
      prependZerosOne_mem_pointedGluingSet B (p (x.val 0)) _
        (σ_n (x.val 0) ⟨_, _⟩).prop⟩,
    gluing_to_pgluing_sigma_cont A B p σ_n hσc, ?_⟩
  refine ⟨fun y => prepend (Function.invFun p (firstNonzero y))
      (τ_n (Function.invFun p (firstNonzero y)) (stripZerosOne (firstNonzero y) y)),
    gluing_to_pgluing_tau_cont A B p hp σ_n hσc τ_n hτc heq, ?_⟩
  -- Equation: x.val = τ((σ x).val)
  intro x
  simp only []
  rw [firstNonzero_prependZerosOne, stripZerosOne_prependZerosOne,
      Function.leftInverse_invFun hp]
  rw [← heq (x.val 0) ⟨unprepend x.val, unprepend_mem_of_gluingSet A x⟩]
  exact (prepend_unprepend x.val).symm

end