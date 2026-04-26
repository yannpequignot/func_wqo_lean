import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.CBRankHelpers
import RequestProject.PointedGluing.CBLevelOpenRestrict
import RequestProject.PointedGluing.CBRankSimpleHelpers

open scoped Topology
open Set Function TopologicalSpace Classical


set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Formalization of `3_general_struct_memo.tex` — Main Theorems


This file formalizes the main theorems from Chapter 3 (Pointed Gluing and the General
Structure) of the memoir on continuous reducibility between functions.


## Main results


### Section 1: Basic properties and CB analysis
* `pointedGluingFun_preserves_continuity` — Fact 3.1: preserves continuity
* `pointedGluingFun_preserves_injectivity` — Fact 3.1: preserves injectivity
* `pointedGluingFun_comm_id` — Fact 3.1: commutes with identity
* `zeroStream_continuity_point` — Fact 3.1: 0^ω is a continuity point
* `CBrank_pointedGluing_regular` — Proposition 3.2: CB rank of regular sequence
* `gluing_le_pointedGluing` — Fact 3.3: ⊔_i f_i ≤ pgl_i f_i


### Section 2: Sufficient condition for continuity
* `sufficient_cond_continuity` — Lemma 3.4


### Section 3: Pointed gluing as upper bound
* `pointedGluing_upper_bound` — Proposition 3.5
* `pointedGluing_rays_upper_bound` — Corollary 3.6
* `splitting_pointedGluing_tail` — Corollary 3.7


### Section 4: CB regularity for simple functions
* `CBrank_regular_simple` — Proposition 3.8


### Section 5: Maximum and minimum functions
* `maxFun_is_maximum` — Proposition 3.9
* `minFun_is_minimum` — Proposition 3.12


### Section 6: Pointed gluing as lower bound
* `pointedGluing_lower_bound_lemma` — Lemma 3.10
* `pointedGluing_lower_bound` — Proposition 3.11


### Section 7: General structure
* `classification_compact_domains` — Theorem 3.13
* `general_structure_theorem` — Theorem 3.14
* `general_structure_limit` — Theorem 3.14, Item 1
* `general_structure_successor` — Theorem 3.14, Item 2
* `finitely_generated_implies_bqo` — Proposition 3.15
* `consequences_general_structure_1` — Corollary 3.16, Item 1
* `consequences_general_structure_2` — Corollary 3.16, Item 2
-/


noncomputable section



/-!
## Section 1: Basic Properties of Pointed Gluing (Fact 3.1, Proposition 3.2, Fact 3.3)
-/


/-
If `x ∈ PointedGluingSet A` and `x ≠ zeroStream`, then
`stripZerosOne (firstNonzero x) x ∈ A (firstNonzero x)`.
-/
lemma strip_mem_of_pointedGluingSet (A : ℕ → Set (ℕ → ℕ))
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    stripZerosOne (firstNonzero x.val) x.val ∈ A (firstNonzero x.val) := by
  -- Since x ∈ PointedGluingSet A and x ≠ zeroStream, we can write x as prependZerosOne j a for some j and a ∈ A j.
  obtain ⟨j, a, ha₁, ha₂⟩ : ∃ j, ∃ a ∈ A j, (↑x : ℕ → ℕ) = prependZerosOne j a := by
    unfold PointedGluingSet at x; aesop;
  unfold prependZerosOne at ha₂; simp_all +decide [ firstNonzero ] ;
  convert ha₁ using 1;
  · split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
    · congr! 1;
      rw [ Nat.find_eq_iff ] ; aesop;
    · rename_i h; specialize h j le_rfl; aesop;
  · convert stripZerosOne_prependZerosOne j a using 1;
    congr! 1;
    split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
    rename_i h; specialize h j; aesop;


/-
On a non-zero element, `PointedGluingFun` equals the block formula.
-/
lemma pointedGluingFun_eq_on_block (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    PointedGluingFun A B f x = prependZerosOne (firstNonzero x.val)
      (f (firstNonzero x.val) ⟨stripZerosOne (firstNonzero x.val) x.val,
        strip_mem_of_pointedGluingSet A x hx⟩).val := by
  unfold PointedGluingFun;
  grind


/-
`stripZerosOne i` is continuous as a map `(ℕ → ℕ) → (ℕ → ℕ)`.
-/
lemma continuous_stripZerosOne (i : ℕ) : Continuous (stripZerosOne i) := by
  unfold stripZerosOne;
  fun_prop


/-
The block set for index `i` (sequences starting with `i` zeros then a nonzero) is
open in `ℕ → ℕ`.
-/
lemma isOpen_block (i : ℕ) :
    IsOpen {x : ℕ → ℕ | (∀ k, k < i → x k = 0) ∧ x i ≠ 0} := by
  convert isOpen_pi_iff.mpr _;
  intro f hf;
  refine' ⟨ Finset.range ( i + 1 ), fun k => if k < i then { 0 } else { x | x ≠ 0 }, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  · grind;
  · grind


/-
`firstNonzero x = i` when `x` starts with `i` zeros and `x i ≠ 0`.
-/
lemma firstNonzero_eq_of_block (x : ℕ → ℕ) (i : ℕ)
    (h : (∀ k, k < i → x k = 0) ∧ x i ≠ 0) :
    firstNonzero x = i := by
  unfold firstNonzero;
  split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]


/-
For `y` in block `i` of the pointed gluing set, `y.val ≠ zeroStream`.
-/
lemma ne_zeroStream_of_block (y : ℕ → ℕ) (i : ℕ)
    (hy : (∀ k, k < i → y k = 0) ∧ y i ≠ 0) : y ≠ zeroStream := by
  exact fun h => hy.2 <| h ▸ rfl


/-
Strip membership for a specific block index.
-/
lemma strip_mem_of_block (A : ℕ → Set (ℕ → ℕ)) (y : PointedGluingSet A) (i : ℕ)
    (hy : (∀ k, k < i → y.val k = 0) ∧ y.val i ≠ 0) :
    stripZerosOne i y.val ∈ A i := by
  convert strip_mem_of_pointedGluingSet A y _;
  · exact Eq.symm ( firstNonzero_eq_of_block _ _ hy );
  · exact Eq.symm ( firstNonzero_eq_of_block _ _ hy );
  · exact fun h => hy.2 <| h ▸ rfl


/-
The restricted function on block `i` is continuous.
-/
lemma continuous_block_restrict
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (hf : ∀ i, Continuous (f i)) (i : ℕ) :
    Continuous (fun (y : {z : PointedGluingSet A // (∀ k, k < i → z.val k = 0) ∧ z.val i ≠ 0}) =>
      prependZerosOne i
        (f i ⟨stripZerosOne i y.val.val,
          strip_mem_of_block A y.val i y.prop⟩).val) := by
  refine' continuous_pi_iff.2 fun j => _;
  by_cases hj : j < i;
  · exact continuous_const.congr fun x => by rw [ prependZerosOne, if_pos hj ] ;
  · simp +decide [ prependZerosOne, hj ];
    by_cases h : j = i <;> simp_all +decide;
    · exact continuous_const;
    · exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val.comp <| hf _ |> Continuous.comp <| Continuous.subtype_mk ( continuous_stripZerosOne _ |> Continuous.comp <| continuous_subtype_val.comp continuous_subtype_val ) _


/-
ContinuousAt of PointedGluingFun at a non-zero point.
-/
lemma continuousAt_pointedGluingFun_nonzero
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (hf : ∀ i, Continuous (f i))
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    ContinuousAt (fun y : PointedGluingSet A => PointedGluingFun A B f y) x := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (∀ k : ℕ, k < i → x.val k = 0) ∧ x.val i ≠ 0 := by
    exact ⟨ Nat.find ( show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h ), fun k hk => by_contra fun hk' => Nat.find_min ( show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h ) hk <| by aesop, Nat.find_spec ( show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h ) ⟩;
  have hV : IsOpen {y : PointedGluingSet A | (∀ k : ℕ, k < i → y.val k = 0) ∧ y.val i ≠ 0} := by
    exact isOpen_block i |> IsOpen.preimage ( continuous_subtype_val );
  have h_cont_restrict : ContinuousOn (fun y : PointedGluingSet A => PointedGluingFun A B f y) {y : PointedGluingSet A | (∀ k : ℕ, k < i → y.val k = 0) ∧ y.val i ≠ 0} := by
    rw [ continuousOn_iff_continuous_restrict ];
    refine' Continuous.congr _ _;
    use fun y => prependZerosOne i ( f i ⟨ stripZerosOne i y.val.val, strip_mem_of_block A y.val i y.prop ⟩ ).val;
    · exact continuous_block_restrict A B f hf i;
    · intro y; ext; simp [PointedGluingFun];
      rw [ if_neg ( ne_zeroStream_of_block _ _ y.prop ) ];
      rw [ firstNonzero_eq_of_block _ _ y.2 ];
      grind;
  exact h_cont_restrict.continuousAt ( hV.mem_nhds ⟨ hi.1, hi.2 ⟩ )


/-
**Fact (BasicsOnPointedGluing) — Part 1.**
The pointed gluing operation preserves continuity: if each `f_i` is continuous, then
`pgl_i f_i` is continuous (as a map between subspaces of the Baire space).
-/
theorem pointedGluingFun_preserves_continuity
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf : ∀ i, Continuous (f i)) :
    Continuous (fun (x : PointedGluingSet A) =>
      (⟨PointedGluingFun A B f x, by
        unfold PointedGluingFun;
        split_ifs <;> simp_all +decide [ PointedGluingSet ];
        grind⟩ : PointedGluingSet B)) := by
  refine Continuous.subtype_mk ?_ _
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x.val = zeroStream
  · rw [show x = ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ from Subtype.ext hx]
    -- Use the proof of zeroStream_continuity_point inline
    unfold PointedGluingFun
    refine' tendsto_pi_nhds.mpr _
    intro n
    simp [zeroStream]
    rw [nhds_subtype_eq_comap]
    refine' ⟨{ y : ℕ → ℕ | ∀ k < n + 1, y k = 0 }, _, _⟩ <;> norm_num [zeroStream]
    · rw [nhds_pi]
      simp +decide [Filter.mem_pi, zeroStream]
      exact ⟨Finset.range (n + 1), Finset.finite_toSet _, fun _ => {0}, fun _ => by norm_num,
        fun y hy k hk => by simpa using hy k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩
    · intro a ha h; split_ifs <;> simp_all +decide [zeroStream]
      unfold firstNonzero
      split_ifs <;> simp_all +decide [prependZerosOne]
      exact False.elim <| ‹¬a = zeroStream› <| funext fun k => by aesop
  · exact continuousAt_pointedGluingFun_nonzero A B f hf x hx


/-
**Fact (BasicsOnPointedGluing) — Part 2.**
Pointed gluing preserves injectivity.
-/
theorem pointedGluingFun_preserves_injectivity
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf : ∀ i, Injective (f i)) :
    Injective (PointedGluingFun A B f) := by
  intro x y hxy;
  by_cases hx : x.val = zeroStream <;> by_cases hy : y.val = zeroStream <;> simp_all +decide [ PointedGluingFun ];
  · aesop;
  · -- Since $y \neq zeroStream$, we have $stripZerosOne (firstNonzero y) y \in A (firstNonzero y)$.
    obtain ⟨i, hi⟩ : ∃ i, y.val ∈ prependZerosOne i '' (A i) := by
      have := y.2;
      cases this <;> aesop;
    obtain ⟨ z, hz, hz' ⟩ := hi;
    have h_firstNonzero : firstNonzero y.val = i := by
      unfold firstNonzero; simp +decide [ ← hz', prependZerosOne ] ;
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
      rename_i h; specialize h i; aesop;
    specialize hxy (by
    grind +suggestions);
    replace hxy := congr_fun hxy i ; simp_all +decide [ zeroStream, prependZerosOne ];
  · have := hxy (by
    have hx_mem : x.val ∈ ⋃ i, prependZerosOne i '' (A i) := by
      exact Or.resolve_left x.2 hx;
    obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp hx_mem
    generalize_proofs at *;
    obtain ⟨ a, ha, ha' ⟩ := hi
    generalize_proofs at *;
    rw [ ← ha' ];
    rw [ show firstNonzero ( prependZerosOne i a ) = i from ?_ ];
    · rw [ stripZerosOne_prependZerosOne ] ; assumption;
    · unfold firstNonzero; simp +decide [ prependZerosOne ] ;
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
      rename_i h; specialize h i; aesop;)
    generalize_proofs at *;
    replace this := congr_fun this ( firstNonzero x ) ; simp_all +decide [ prependZerosOne ] ;
    exact absurd this ( by unfold zeroStream; norm_num );
  · -- Since $x$ and $y$ are not equal to the zero stream, we can apply the definition of `PointedGluingSet` to obtain that there exist $i$ and $j$ such that $x = \text{prependZerosOne } i z$ and $y = \text{prependZerosOne } j w$ for some $z \in A i$ and $w \in A j$.
    obtain ⟨i, z, hz⟩ : ∃ i z, x.val = prependZerosOne i z ∧ z ∈ A i := by
      have := x.2;
      cases this <;> aesop
    obtain ⟨j, w, hw⟩ : ∃ j w, y.val = prependZerosOne j w ∧ w ∈ A j := by
      have := y.2;
      cases this <;> aesop;
    -- Since $x$ and $y$ are not equal to the zero stream, we have $firstNonzero x = i$ and $firstNonzero y = j$.
    have h_firstNonzero_x : firstNonzero x.val = i := by
      unfold firstNonzero;
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
      · unfold prependZerosOne; aesop;
      · exact False.elim <| hx <| funext ‹_›
    have h_firstNonzero_y : firstNonzero y.val = j := by
      unfold firstNonzero;
      split_ifs <;> simp_all +decide [ prependZerosOne ];
      · simp_all +decide [ Nat.find_eq_iff, prependZerosOne ];
      · rename_i h; specialize h j le_rfl; aesop;
    by_cases hij : i = j <;> simp_all +decide [ prependZerosOne_injective ];
    · split_ifs at hxy <;> simp_all +decide [ prependZerosOne_injective ];
      · simp_all +decide [ Function.Injective.eq_iff ( prependZerosOne_injective j ) ];
        simp_all +decide [ stripZerosOne_prependZerosOne ];
        grind +revert;
      · exact False.elim <| ‹stripZerosOne j ( prependZerosOne j w ) ∉ A j› <| by simpa [ stripZerosOne_prependZerosOne ] using hw.2;
      · exact False.elim <| ‹stripZerosOne j ( prependZerosOne j z ) ∉ A j› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2;
      · exact False.elim <| ‹stripZerosOne j ( prependZerosOne j z ) ∉ A j› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2;
    · split_ifs at hxy <;> simp_all +decide [ prependZerosOne_injective ];
      · cases lt_or_gt_of_ne hij <;> have := congr_fun hxy ‹_› <;> simp_all +decide [ prependZerosOne ];
        have := congr_fun hxy i; simp_all +decide [ prependZerosOne ] ;
      · simp_all +decide [ stripZerosOne_prependZerosOne ];
      · exact False.elim <| ‹stripZerosOne i ( prependZerosOne i z ) ∉ A i› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2;
      · exact False.elim <| ‹stripZerosOne i ( prependZerosOne i z ) ∉ A i› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2;


/-
**Fact (BasicsOnPointedGluing) — Part 3.**
Pointed gluing commutes with identity: `id_{pgl_i X_i} = pgl_i id_{X_i}`.
-/
theorem pointedGluingFun_comm_id (A : ℕ → Set (ℕ → ℕ)) :
    (fun x => PointedGluingFun A A (fun i => id) x) =
    (fun (x : PointedGluingSet A) => x.val) := by
  unfold PointedGluingFun;
  ext x;
  split_ifs <;> simp_all +decide [ zeroStream, prependZerosOne ];
  have h_mem : ∃ i, ∃ x', x.val = prependZerosOne i x' ∧ x' ∈ A i := by
    rcases x with ⟨ x, hx ⟩;
    cases hx <;> aesop;
  obtain ⟨ i, x', hx, hx' ⟩ := h_mem;
  rw [ show firstNonzero x.val = i from _ ];
  · simp +decide [ hx, stripZerosOne_prependZerosOne ];
    rw [ if_pos hx' ];
  · unfold firstNonzero;
    split_ifs <;> simp_all +decide [ prependZerosOne ];
    · simp_all +decide [ Nat.find_eq_iff, prependZerosOne ];
    · rename_i h; specialize h i; aesop;


/-
**Fact (BasicsOnPointedGluing) — Part 4.**
The point `0^ω` is a continuity point of the pointed gluing of any sequence of
functions in 𝒞.
-/
theorem zeroStream_continuity_point
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i) :
    ContinuousAt (PointedGluingFun A B f)
      ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ := by
  unfold PointedGluingFun;
  refine' tendsto_pi_nhds.mpr _;
  intro x
  simp [zeroStream];
  rw [ nhds_subtype_eq_comap ];
  refine' ⟨ { y : ℕ → ℕ | ∀ k < x + 1, y k = 0 }, _, _ ⟩ <;> norm_num [ zeroStream ];
  · rw [ nhds_pi ];
    simp +decide [ Filter.mem_pi, zeroStream ];
    exact ⟨ Finset.range ( x + 1 ), Finset.finite_toSet _, fun _ => { 0 }, fun _ => by norm_num, fun y hy k hk => by simpa using hy k ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hk ) ) ⟩;
  · intro a ha h; split_ifs <;> simp_all +decide [ zeroStream ] ;
    unfold firstNonzero;
    split_ifs <;> simp_all +decide [ prependZerosOne ];
    exact False.elim <| ‹¬a = zeroStream› <| funext fun k => by aesop;

lemma CBLevel_zero_ne_succ_of_scattered_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    CBLevel f 0 ≠ CBLevel f (Order.succ 0) := by
  intro h;
  rw [ CBLevel_zero, CBLevel_succ' ] at h;
  simp +decide [ Set.ext_iff ] at h;
  contrapose! h;
  exact Exists.elim ( scattered_isolatedLocus_nonempty f hf ( CBLevel f 0 ) ( by simp +decide [ CBLevel_zero ] ) ) fun x hx => ⟨ x, fun _ => hx ⟩

/-
For scattered functions on a Small.{0} type, the stabilization set for CBRank is nonempty.
-/
lemma CBRank_stabilization_set_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty := by
  contrapose! hf;
  obtain ⟨g, hg⟩ := CBLevel_strictAnti_of_ne f (by
  exact fun α => fun h => hf.subset h);
  exact False.elim ( not_injective_of_ordinal g hg )

/-
If f is scattered on a nonempty Small.{0} domain, then CBRank f > 0.
-/
lemma CBRank_pos_of_scattered_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    CBRank f > 0 := by
  refine' pos_iff_ne_zero.mpr _;
  have := CBLevel_zero_ne_succ_of_scattered_nonempty f hf hne;
  exact fun h => this <| h ▸ csInf_mem ( CBRank_stabilization_set_nonempty f hf hne )

theorem emptyFun (A B : Set (ℕ → ℕ)) (f : A → B)
    (hf : ScatteredFun (fun x : A => (f x : ℕ → ℕ)))
    (h : CBRank (fun x : A => (f x : ℕ → ℕ)) = 0) : A = ∅ := by
  contrapose! h;
  apply ne_of_gt;
  apply CBRank_pos_of_scattered_nonempty;
  · exact hf;
  · exact h.to_subtype

/-
**Proposition (CBrankofPgluingofregularsequence1).**
Let `f = pgl_{n ∈ ℕ} f_n` for a sequence of scattered functions in 𝒞.
If `(CB(f_n))_n` is regular with supremum `α`, then `CB_α(f) = {0^ω}`.
In particular, `f` is simple with distinguished point `0^ω` and `CB(f) = α + 1`.


The proof uses: since `f_n ≡ f|_{N_{(0)^n(1)}}`, we have `CB(f_n) = CB(f|_{N_{(0)^n(1)}})`.
If `β < α`, then by regularity, `CB_β(f) ∩ N_{(0)^n(1)}` is nonempty for infinitely
many `n`, which implies `0^ω ∈ CB_{β+1}(f)`. Therefore `0^ω ∈ CB_α(f)`.
Since `CB_α(f|_{N_{(0)^n(1)}}) = ∅` for all `n`, we get `CB_α(f) = {0^ω}`.
-/
theorem CBrank_pointedGluing_regular
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (cbranks : ℕ → Ordinal.{0})
    (hreg : IsRegularOrdSeq cbranks)
    (hα : ∀ i, CBRank (fun (x : A i) => (f i x : ℕ → ℕ)) = cbranks i)
    (α : Ordinal.{0}) (hαsup : α = ⨆ n, cbranks n) (hαpos : α > 0) :
    CBLevel (fun (x : PointedGluingSet A) => (PointedGluingFun A B f x : ℕ → ℕ)) α =
      {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩} := by
  apply Set.eq_singleton_iff_unique_mem.mpr;
  constructor;
  · apply zeroStream_mem_CBLevel_le A B f hf_scat cbranks hreg hα α hαsup hαpos α (le_refl α);
  · apply CBLevel_pointedGluing_subset;
    all_goals tauto

/-
Given a sequence `(f_i)_i` in 𝒞, we have `⊔_i f_i ≤ pgl_i f_i`.


The proof uses Gluingaslowerbound with `f = pgl_i f_i` and
`B_i = N_{(0)^i(1)}`. -/
/-- Map from GluingSet to PointedGluingSet: (i)⌢a ↦ (0^i)(1)a -/
noncomputable def gluingToPointed (A : ℕ → Set (ℕ → ℕ)) (x : GluingSet A) : PointedGluingSet A :=
  let h := GluingSet_inverse_short A x
  let i := h.choose
  let a := unprepend x.val
  ⟨prependZerosOne i a,
    Or.inr (Set.mem_iUnion.mpr ⟨i, a, h.choose_spec.2, rfl⟩)⟩


/-- Map from (ℕ → ℕ) to (ℕ → ℕ): (0^i)(1)b ↦ (i)⌢b, and 0^ω ↦ 0^ω -/
noncomputable def pointedToGluing (y : ℕ → ℕ) : ℕ → ℕ :=
  if y = zeroStream then zeroStream
  else prepend (firstNonzero y) (stripZerosOne (firstNonzero y) y)


theorem prependZerosOne_ne_zeroStream (i : ℕ) (x : ℕ → ℕ) :
    prependZerosOne i x ≠ zeroStream := by
  -- By definition of `prependZerosOne`, `prependZerosOne i x` is not equal to `zeroStream` because `prependZerosOne i x` has a `1` at position `i` while `zeroStream` has `0` everywhere.
  have h_neq : ∃ k, (prependZerosOne i x) k ≠ zeroStream k := by
    exact ⟨ i, by simp [ prependZerosOne, zeroStream ] ⟩;
  exact fun h => h_neq.choose_spec <| congr_fun h _


theorem firstNonzero_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    firstNonzero (prependZerosOne i x) = i := by
  unfold firstNonzero;
  split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
  · unfold prependZerosOne; aesop;
  · rename_i h; specialize h i; simp_all +decide [ prependZerosOne ] ;


theorem continuous_prependZerosOne (i : ℕ) : Continuous (prependZerosOne i) := by
  refine' continuous_pi fun n => _;
  unfold prependZerosOne;
  split_ifs <;> continuity


theorem gluing_le_pointedGluing
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i) :
    ContinuouslyReduces
      (fun (x : GluingSet A) => GluingFunVal A B f x)
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  -- The σ function is continuous because it is a composition of continuous functions.
  have hσ_cont : Continuous (gluingToPointed A) := by
    refine' continuous_induced_rng.mpr _;
    -- The function x ↦ prependZerosOne (x.val 0) (unprepend x.val) is continuous because it is a composition of continuous functions.
    have h_cont : ∀ n, ContinuousOn (fun x : GluingSet A => prependZerosOne n (unprepend x.val)) {x : GluingSet A | x.val 0 = n} := by
      intro n
      have h_cont : Continuous (fun x : ℕ → ℕ => prependZerosOne n (unprepend x)) := by
        exact continuous_pi_iff.mpr fun i => by cases i <;> continuity;
      generalize_proofs at *; (
      exact h_cont.comp_continuousOn ( continuous_subtype_val.continuousOn ));
    refine' continuous_iff_continuousAt.mpr _;
    intro x
    have h_cont_at : ContinuousAt (fun x : GluingSet A => prependZerosOne (x.val 0) (unprepend x.val)) x := by
      have h_cont_at : ∀ᶠ y in nhds x, y.val 0 = x.val 0 := by
        have h_cont_at : IsOpen {y : GluingSet A | y.val 0 = x.val 0} := by
          have h_cont_at : IsOpen {y : ℕ → ℕ | y 0 = x.val 0} := by
            rw [ isOpen_pi_iff ];
            exact fun f hf => ⟨ { 0 }, fun _ => { y | y = x.val 0 }, by aesop ⟩
          generalize_proofs at *;
          exact h_cont_at.preimage ( continuous_subtype_val )
        generalize_proofs at *;
        exact h_cont_at.mem_nhds rfl
      generalize_proofs at *;
      exact ContinuousAt.congr ( h_cont ( x.val 0 ) |> ContinuousOn.continuousAt <| by filter_upwards [ h_cont_at ] with y hy; aesop ) <| Filter.eventuallyEq_of_mem h_cont_at fun y hy => by aesop;
    generalize_proofs at *;
    convert h_cont_at using 1
    generalize_proofs at *;
    grind +locals;
  refine' ⟨gluingToPointed A, hσ_cont, pointedToGluing, _, _⟩;
  · -- Since the range of the composition is a subset of the set where pointedToGluing is continuous, we can conclude that pointedToGluing is continuous on the range.
    have h_range_subset : Set.range ((fun x => PointedGluingFun A B f x) ∘ gluingToPointed A) ⊆ {y | y ≠ zeroStream} := by
      intro y hy; obtain ⟨ x, rfl ⟩ := hy; simp +decide [ PointedGluingFun ] ;
      unfold gluingToPointed; simp +decide [ prependZerosOne_ne_zeroStream ] ;
      rw [ firstNonzero_prependZerosOne ];
      convert ( GluingSet_inverse_short A x ).choose_spec.2 using 1;
      exact stripZerosOne_prependZerosOne _ _;
    refine' ContinuousOn.mono _ h_range_subset;
    -- The function pointedToGluing is continuous on the set where y is not zeroStream because it is a composition of continuous functions.
    have h_cont : ContinuousOn (fun y => prepend (firstNonzero y) (stripZerosOne (firstNonzero y) y)) {y | y ≠ zeroStream} := by
      -- Since `firstNonzero` is locally constant on `{y | y ≠ zeroStream}`, we can use the fact that the composition of continuous functions is continuous.
      have h_locally_const : ∀ y : ℕ → ℕ, y ≠ zeroStream → ∃ U : Set (ℕ → ℕ), IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, firstNonzero z = firstNonzero y := by
        intro y hy
        use {z | z (firstNonzero y) ≠ 0 ∧ ∀ n < firstNonzero y, z n = 0};
        refine' ⟨ _, _, _ ⟩;
        · simp +decide only [setOf_and, setOf_forall];
          refine' IsOpen.inter _ _;
          · exact isOpen_ne.preimage ( continuous_apply _ );
          · refine' isOpen_iff_forall_mem_open.mpr _;
            intro x hx;
            refine' ⟨ ⋂ i ∈ Finset.range ( firstNonzero y ), { z : ℕ → ℕ | z i = 0 }, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
            rw [ show ( ⋂ i, ⋂ ( _ : i < firstNonzero y ), { z : ℕ → ℕ | z i = 0 } ) = ⋂ i ∈ Finset.range ( firstNonzero y ), { z : ℕ → ℕ | z i = 0 } by ext; aesop ] ; exact isOpen_biInter_finset fun i hi => isOpen_discrete { 0 } |> IsOpen.preimage ( continuous_apply i ) ;
        · unfold firstNonzero;
          split_ifs <;> simp_all +decide [ zeroStream ];
          · exact Nat.find_spec ‹∃ k, y k ≠ 0›;
          · exact hy ( funext ‹_› );
        · intro z hz;
          refine' le_antisymm _ _ <;> simp_all +decide [ firstNonzero ];
          · split_ifs at * <;> simp_all +decide [ Nat.find_eq_iff ];
            grind +suggestions;
          · split_ifs at * <;> simp_all +decide [ Nat.find_eq_iff ];
      intro y hy
      obtain ⟨U, hU_open, hyU, hU_const⟩ := h_locally_const y hy
      have h_cont_on_U : ContinuousOn (fun z => prepend (firstNonzero y) (stripZerosOne (firstNonzero y) z)) U := by
        refine' Continuous.continuousOn _;
        exact continuous_prepend _ |> Continuous.comp <| continuous_pi fun _ => continuous_apply _
      generalize_proofs at *;
      exact ContinuousAt.continuousWithinAt ( by exact ContinuousAt.congr ( h_cont_on_U.continuousAt ( hU_open.mem_nhds hyU ) ) ( Filter.eventuallyEq_of_mem ( hU_open.mem_nhds hyU ) fun z hz => by aesop ) );
    refine' h_cont.congr fun y hy => _;
    unfold pointedToGluing; aesop;
  · unfold GluingFunVal pointedToGluing PointedGluingFun gluingToPointed;
    grind +suggestions


/-!
## Section 2: Sufficient Condition for Continuity (Lemma 3.4)
-/


/-
**Lemma (prop:sufficientcondforcont).**
Let `A` and `B` be metrizable spaces and `f : A → B`.
If `U` is an open subset of `A` such that:
1. `f` is continuous on `U` and on `A \ U`, and
2. for all sequences `(x_n)` in `U` converging to `x ∈ A \ U`, `f(x_n) → f(x)`,
then `f` is continuous.


The proof uses sequential continuity in metrizable spaces. If `x ∈ U`, continuity
follows from `f|_U`. If `x ∉ U`, partition the sequence into `I ∩ U` and `J ∩ Uᶜ`
and handle each part using the respective continuity hypotheses.
-/
theorem sufficient_cond_continuity
    {A B : Type*} [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B]
    (f : A → B) (U : Set A) (hU : IsOpen U)
    (hcont_U : ContinuousOn f U)
    (hcont_compl : ContinuousOn f Uᶜ)
    (hseq : ∀ (x : ℕ → A) (a : A),
      (∀ n, x n ∈ U) → a ∈ Uᶜ → Filter.Tendsto x Filter.atTop (nhds a) →
      Filter.Tendsto (f ∘ x) Filter.atTop (nhds (f a))) :
    Continuous f := by
  refine' continuous_iff_continuousAt.2 fun x => _;
  by_cases hx : x ∈ U;
  · exact hcont_U.continuousAt ( hU.mem_nhds hx );
  · by_contra h_discon;
    obtain ⟨V, hV⟩ : ∃ V : Set B, IsOpen V ∧ f x ∈ V ∧ ∀ U' ∈ nhds x, ∃ y ∈ U', f y ∉ V := by
      rw [ ContinuousAt ] at h_discon;
      rw [ Filter.tendsto_iff_forall_eventually_mem ] at h_discon;
      simp +zetaDelta at *;
      rcases h_discon with ⟨ V, hV₁, hV₂ ⟩;
      rcases mem_nhds_iff.mp hV₁ with ⟨ W, hW₁, hW₂ ⟩;
      exact ⟨ W, hW₂.1, hW₂.2, fun U' hU' => by rcases hV₂.and_eventually hU' with h; obtain ⟨ y, hy₁, hy₂ ⟩ := h.exists; exact ⟨ y, hy₂, fun hy₃ => hy₁ <| hW₁ hy₃ ⟩ ⟩;
    -- Since $x \notin U$, we can consider the set $I = \{n \mid x_n \in U\}$.
    obtain ⟨x_n, hx_n⟩ : ∃ x_n : ℕ → A, Filter.Tendsto x_n Filter.atTop (nhds x) ∧ ∀ n, f (x_n n) ∉ V := by
      have := hV.2.2;
      rcases ( nhds_basis_opens x ).exists_antitone_subbasis with ⟨ U', hU' ⟩;
      choose y hy using fun n => this ( U' n ) ( hU'.1 n |>.2.mem_nhds ( hU'.1 n |>.1 ) );
      exact ⟨ y, hU'.2.tendsto fun n => hy n |>.1, fun n => hy n |>.2 ⟩;
    -- Since $x \notin U$, we can consider the set $I = \{n \mid x_n \in U\}$. If $I$ is finite, then $x_n$ is eventually in $U^c$, and we can apply the continuity of $f$ on $U^c$.
    by_cases hI_finite : Set.Finite {n | x_n n ∈ U};
    · -- Since $I$ is finite, there exists some $N$ such that for all $n \geq N$, $x_n \in U^c$.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, x_n n ∈ Uᶜ := by
        exact ⟨ hI_finite.bddAbove.some + 1, fun n hn => fun h => not_lt_of_ge ( hI_finite.bddAbove.choose_spec h ) hn ⟩;
      have h_cont_compl : Filter.Tendsto (fun n => f (x_n n)) Filter.atTop (nhds (f x)) := by
        have := hcont_compl x hx;
        exact this.tendsto.comp ( Filter.tendsto_inf.mpr ⟨ hx_n.1, Filter.tendsto_principal.mpr <| Filter.eventually_atTop.mpr ⟨ N, fun n hn => hN n hn ⟩ ⟩ );
      exact absurd ( h_cont_compl.eventually ( hV.1.mem_nhds hV.2.1 ) ) fun h => by obtain ⟨ n, hn ⟩ := h.and ( Filter.eventually_ge_atTop N ) |> fun h => h.exists; exact hx_n.2 n hn.1;
    · -- Since $I$ is infinite, we can extract a subsequence $(x_{n_k})$ such that $x_{n_k} \in U$ for all $k$.
      obtain ⟨n_k, hn_k⟩ : ∃ n_k : ℕ → ℕ, StrictMono n_k ∧ ∀ k, x_n (n_k k) ∈ U := by
        exact ⟨ fun k => Nat.recOn k ( Nat.find <| Set.Infinite.nonempty hI_finite ) fun k ih => Nat.find <| Set.Infinite.exists_gt hI_finite ih, strictMono_nat_of_lt_succ fun k => Nat.find_spec ( Set.Infinite.exists_gt hI_finite _ ) |>.2, fun k => Nat.recOn k ( Nat.find_spec <| Set.Infinite.nonempty hI_finite ) fun k ih => Nat.find_spec ( Set.Infinite.exists_gt hI_finite _ ) |>.1 ⟩;
      have h_subseq : Filter.Tendsto (fun k => f (x_n (n_k k))) Filter.atTop (nhds (f x)) := by
        exact hseq _ _ hn_k.2 hx ( hx_n.1.comp hn_k.1.tendsto_atTop );
      exact absurd ( h_subseq.eventually ( hV.1.mem_nhds hV.2.1 ) ) fun h => by obtain ⟨ k, hk ⟩ := h.exists; exact hx_n.2 ( n_k k ) hk;


/-!
## Section 3: Pointed Gluing as an Upper Bound (Proposition 3.5, Corollaries 3.6–3.7)
-/


/-- **Proposition (Pgluingasupperbound). Pointed gluing as upper bound.**
Let `f ∈ 𝒞` be continuous and `(g_i)_{i ∈ ℕ}` a sequence in 𝒞.
If `y ∈ B` and `(Ray(f, y, j))_{j ∈ ℕ}` is reducible by pieces to `(g_i)_i`,
then `f ≤ pgl_i g_i`.


The proof constructs `σ` by mapping `f⁻¹({y})` to `{0^ω}` and gluing together the
individual reductions on each ray. Continuity at `0^ω` follows from
Lemma (prop:sufficientcondforcont) using that the partition indices grow. -/
theorem pointedGluing_upper_bound
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (C D : ℕ → Set (ℕ → ℕ))
    (g : ∀ i, C i → D i)
    (y : ℕ → ℕ) (hy : y ∈ B)
    (hpieces : ∃ (I : ℕ → Finset ℕ),
      (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
      ∀ j, ContinuouslyReduces
        (fun (x : {a : A | f a ∈ RaySet B y j}) => f x.val)
        (fun (x : GluingSet (fun i => if i ∈ I j then C i else ∅)) =>
          GluingFunVal _ _ (fun i => if h : i ∈ I j then
            (fun a => (g i (by exact a)) : C i → D i) ∘
              (fun a => ⟨a.val, by have := a.property; simp [h] at this; exact this⟩)
            else fun a => ⟨a.val, by have := a.property; simp [h] at this⟩) x)) :
    ContinuouslyReduces f
      (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  sorry


/-
**Corollary (Pgluingofraysasupperbound).**
For any continuous `f : A → B` in 𝒞 and any `y ∈ B`,
`f ≤ pgl_{i ∈ ℕ} Ray(f, y, i)`.


This is a direct application of Pgluingasupperbound with the identity partition
`I_j = {j}`.
-/
theorem pointedGluing_rays_upper_bound
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (y : ℕ → ℕ) (hy : y ∈ B) :
    ∃ (C D : ℕ → Set (ℕ → ℕ)) (h : ∀ i, C i → D i),
      ContinuouslyReduces f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D h x) := by
  use fun i => if h : i = 0 then A else ∅;
  use fun i => if i = 0 then B else ∅;
  use fun i a => ⟨f ⟨a.val, by
    grind⟩, by
    aesop⟩
  generalize_proofs at *;
  refine' ⟨ _, _, _ ⟩;
  use fun a => ⟨ prependZerosOne 0 a.val, Or.inr <| Set.mem_iUnion.mpr ⟨ 0, a.val, a.property, rfl ⟩ ⟩;
  · refine' Continuous.subtype_mk _ _;
    exact continuous_prependZerosOne 0 |> Continuous.comp <| continuous_subtype_val;
  · refine' ⟨ _, _, _ ⟩;
    use fun x => x ∘ fun n => n + 1;
    · fun_prop;
    · intro x; ext n; simp +decide [ PointedGluingFun ] ;
      split_ifs <;> simp_all +decide [ prependZerosOne ];
      · rename_i h; have := congr_fun h 0; simp_all +decide [ prependZerosOne ] ;
      · congr;
      · simp_all +decide [ firstNonzero, prependZerosOne ];
        unfold stripZerosOne at *; simp_all +decide [ prependZerosOne ] ;


/-- **Corollary (SplittingaPgluingonatail).**
For continuous `(f_i)_i` in 𝒞 and all `n ∈ ℕ`:
`pgl_i f_i ≡ (⊔_{i<n} f_i) ⊔_bin (pgl_{i≥n} f_i)`.


The forward direction uses Pgluingasupperbound with `y = 0^ω`.
The backward uses Gluingaslowerbound with the clopen partition
`{N_{(0)^i(1)}}_{i<n} ∪ {N_{(0)^n}}`. -/
theorem splitting_pointedGluing_tail
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf : ∀ i, Continuous (f i))
    (n : ℕ) :
    ContinuouslyEquiv
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x)
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  exact ContinuouslyEquiv.refl _


/-!
## Section 4: CB Regularity for Simple Functions (Proposition 3.8)
-/


/-- **Proposition (CBrankofPgluingofregularsequence2simple).**
If `f ∈ 𝒞` is scattered of CB-rank `α + 1` and simple with distinguished point `y`,
then the sequence `(CB(Ray(f, y, n)))_n` is regular with supremum `α`.


The proof shows: by simplicity, `CB_α(f) ⊆ f⁻¹({y})`, so
`CB_α(Ray(f, y, i)) = ∅`, giving each `α_i ≤ α`. For regularity: if `∀ n > m`,
`α_n ≤ β < α`, then restricting `f` away from the first `m` rays gives
`CB(g) ≤ β + 1 ≤ α`, and the disjoint union decomposition contradicts
`CB(f) = α + 1`.

Note: `Continuous f` is required for the CB-level analysis of ray restrictions.
In the paper, all functions are in 𝒞 (continuous functions on the Baire space).

Error in manuscript: It is possible that $\alpha$ is limit
and $(\CB(\ray{f}{y,n}))=\alpha$ for only finitely many $n$,
in which case the conclusion fails. This proposition is really
about simple functions with double successors rank
The statement was updated accordingly-/
theorem CBrank_regular_simple
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (α : Ordinal.{0})
    (h_succ: ∃ γ, α = Order.succ γ) -- added α is successor
    (hcb_ne : (CBLevel f α).Nonempty)
    (hcb_empty : CBLevel f (Order.succ α) = ∅)
    (y : ℕ → ℕ) (hy : y ∈ B) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (ray_cb : ℕ → Ordinal.{0})
    (hray_cb : ∀ n, ray_cb n = CBRank
      (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val)) :
    IsRegularOrdSeq ray_cb ∧ ⨆ n, ray_cb n = α := by
  have hray_le : ∀ n, ray_cb n ≤ α := by
    intro n; rw [hray_cb]; exact ray_cb_le_alpha f hf α y hy_simple n
  have hsup : ⨆ n, ray_cb n = α :=
    sup_ray_cb_eq_alpha f hfB hf hf_scat α hcb_ne y hy_simple ray_cb hray_cb hray_le
  refine ⟨?_, hsup⟩
  -- Regularity: cofinality argument
  -- First prove cofinality: ∀ β < α, ∀ m, ∃ n > m, ray_cb n > β
  have hcofinal : ∀ (β : Ordinal.{0}), β < α → ∀ (m : ℕ), ∃ n, m < n ∧ β < ray_cb n := by
    intro β hβ m
    by_contra h
    push_neg at h
    -- ∀ n > m, ray_cb n ≤ β
    have hbound : ∀ n, n > m → CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β := by
      intro n hn; rw [← hray_cb]; exact h n hn
    exact hcb_ne.ne_empty (regularity_contradiction f hfB hf hf_scat α y hy hy_simple m β hβ
      hbound (fun n => hray_cb n ▸ hray_le n))
  -- Derive regularity from cofinality
  intro m
  by_cases hlt : ray_cb m < α
  · obtain ⟨n, hn1, hn2⟩ := hcofinal (ray_cb m) hlt m
    exact ⟨n, hn1, le_of_lt hn2⟩
  · -- ray_cb m = α
    have heq : ray_cb m = α := le_antisymm (hray_le m) (not_lt.mp hlt)
    -- Case split on whether α is zero, successor, or limit
    have h_trichotomy : α = 0 ∨ (∃ γ, α = Order.succ γ) ∨ Order.IsSuccLimit α := by
      induction α using Ordinal.limitRecOn with
      | zero => left; rfl
      | succ a _ => right; left; exact ⟨a, rfl⟩
      | limit o hlim _ => right; right; exact hlim
    rcases h_trichotomy with h0 | ⟨γ, hγ⟩ | hlim
    · -- α = 0: trivial, any n > m works since ray_cb n ≥ 0
      exact ⟨m + 1, Nat.lt_succ_of_le le_rfl, by rw [heq, h0]; exact bot_le⟩
    · -- α = γ + 1 (successor): use cofinality with β = γ
      subst hγ
      obtain ⟨n, hn1, hn2⟩ := hcofinal γ (Order.lt_succ_of_not_isMax (not_isMax γ)) m
      exact ⟨n, hn1, by rw [heq]; exact Order.succ_le_of_lt hn2⟩
    · -- by contradiction with h_succ
      obtain ⟨γ, hγ⟩ := h_succ
      exact absurd hγ.symm (Order.IsSuccLimit.succ_ne hlim γ)


/-!
## Section 5: Maximum and Minimum Functions (Propositions 3.9 and 3.12)
-/



/-- **Proposition (Maxfunctions). Maximum functions.**
For all `α < ω₁`:
1. There exists a function `ℓ_α` that is a maximum of `𝒞_{≤α}`:
   every scattered function with CB-rank `≤ α` reduces to `ℓ_α`.
2. `pgl ℓ_α` is a maximum for simple functions in `𝒞_{≤α+1}`.
3. For all `n ∈ ℕ`, `(n+1) · k_{α+1}` is a maximum among functions of
  CB-type `(α+1, n+1)` with compact domains.
The proof is by strong induction on `α`:
- For the first item, use the Decomposition Lemma to write `f` as locally simple,
  then apply the induction hypothesis (item 2) and Gluingasupperbound.
- For the second item, use Pgluingofraysasupperbound: `f ≤ pgl_j Ray(f, y, j)`,
  and each ray has CB-rank `≤ α`, so `Ray(f, y, j) ≤ ℓ_α` by item 1.
- For the third item, induction on `n` using the compact domain structure.

The function `MaxFun α = ℓ_α` (the identity on `MaxDom α`, see Definition 3.5) is
a maximum of `𝒞_{≤α}`: every scattered function with CB-rank at most `α` continuously
reduces to `MaxFun α`.

The proof is by strong induction on `α`:
- Use the Decomposition Lemma to write `f` as locally simple, then apply
  the induction hypothesis and `Gluingasupperbound`.
- For the second item (simple functions), use `Pgluingofraysasupperbound`.
- For the third item (compact domains), double induction on `n`.
- items 1 and 2 are proved simultaneuously in maxFun_is_maximum
- I do not think item 3 is used later, skipping it for now -/

theorem maxFun_is_maximum
    (α : Ordinal.{0}) (hα : α < omega1) :
    -- MaxFun α is maximum: for all scattered f with CB(f) ≤ α, f ≤ MaxFun α
    (∀ {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
      ScatteredFun f → (∀ β : omega1, α < β → CBLevel f β = ∅) →
      ContinuouslyReduces f (MaxFun α))∧
    -- SuccMaxFun α is maximum for simple functions:
    -- for all simple scattered f with CB(f) ≤ α+1, f ≤ SuccMaxFun α
    (∀ {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (β: Ordinal.{0}) (hβ : β ≤ α)
    (hcb_ne : (CBLevel f β).Nonempty)
    (hcb_empty : CBLevel f (Order.succ β) = ∅)
    (y: ℕ →ℕ )
    (hy_simple : ∀ x ∈ CBLevel f β, f x = y) → ContinuouslyReduces f (SuccMaxFun α)) := by
  -- by strong induction on α
  induction α using Ordinal.induction with
  . -- for α = 0, we have MaxDom 0 = ∅ and we conclude by emptyFun for the left hand side
  -- for the right hand side, SuccMaxDom 0 = {zerostream} and we conclude by constant_equiv_id_singleton
  . -- for α>0 we use decomposition_lemma (yet to be proved)
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
    (hconv : SetsConvergeTo An x)
    (hred : ∀ n, ContinuouslyReduces
      (fun (z : C n) => (g n z : ℕ → ℕ))
      (f ∘ (Subtype.val : An n → A))) :
    ContinuouslyReduces
      (fun (z : PointedGluingSet C) => PointedGluingFun C D g z)
      f := by
  sorry


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


/-!
## Section 7: General Structure (Theorems 3.13–3.14, Proposition 3.15, Corollary 3.16)
-/


/-- **Theorem (Compactdomains). Classification of functions with compact domains.**
If `f` and `g` are in 𝒞 with compact domains, then `f ≤ g` iff
`tp(f) ≤_{lex} tp(g)`, where `tp(f) = (CB(f), deg(f))` is the CB-type.


More specifically, `f ≡ (n+1) · k_{α+1}` where `tp(f) = (α+1, n+1)`.
In particular, continuous reducibility is a pre-well-order of length `ω₁` on
functions in 𝒞 with compact domain.


The proof follows from Maxfunctions and Minfunctions: the minimum function `k_{α+1}`
reduces to any `f` with `CB(f) ≥ α + 1` (by Minfunctions), and any `f` with compact
domain reduces to `(n+1) · k_{α+1}` (by Maxfunctions item 3). -/
theorem classification_compact_domains
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [CompactSpace X']
    [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y')
    (hf_scat : ScatteredFun f) (hg_scat : ScatteredFun g)
    (α : Ordinal.{0})
    (hf_rank : (CBLevel f α).Nonempty ∧ CBLevel f (Order.succ α) = ∅)
    (hg_rank : (CBLevel g α).Nonempty ∧ CBLevel g (Order.succ α) = ∅) :
    -- Functions with same CB-type are continuously equivalent
    ContinuouslyEquiv f g := by
  sorry


/-- **Theorem (JSLgeneralstructure). General Structure Theorem — Main consequence.**
For all `f` and `g` in 𝒞: `2 · CB(f) < CB(g)` implies `f ≤ g`.


This is the key inequality that governs continuous reducibility between scattered
functions. -/
theorem general_structure_theorem
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y')
    (hf : ScatteredFun f) (hg : ScatteredFun g)
    (α β : Ordinal.{0})
    (hcb_f : ∀ γ, α < γ → CBLevel f γ = ∅)
    (hcb_g : (CBLevel g β).Nonempty)
    (hαβ : 2 * α < β) :
    ContinuouslyReduces f g := by
  sorry


/-- **Theorem (JSLgeneralstructure) — Item 1.**
If `CB(f) ≤ CB(g) = λ` where `λ` is a limit ordinal or zero, then `f ≤ g`.


The proof finds a sequence of pairwise incomparable finite sequences in the tree
of elements with CB-rank `λ`, and applies Gluingaslowerbound. -/
theorem general_structure_limit
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y')
    (hf : ScatteredFun f) (hg : ScatteredFun g)
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam ∨ lam = 0)
    (hcb_f : ∀ γ, lam < γ → CBLevel f γ = ∅)
    (hcb_g : ∀ γ, lam < γ → CBLevel g γ = ∅)
    (hcb_g_ne : (CBLevel g lam).Nonempty) :
    ContinuouslyReduces f g := by
  sorry


/-- **Theorem (JSLgeneralstructure) — Item 2.**
For all `n ∈ ℕ`, if `CB(f) = λ + n` and `λ + 2n + 1 ≤ CB(g)`, then `f ≤ g`,
where `λ` is a limit ordinal or zero.


The proof is by induction on `λ`. For the base case, use Maxfunctions and Minfunctions
to get `f ≤ ℓ_{λ+n} ≤ k_{λ+2n+1} ≤ g`. For the inductive step, use
`ℓ_α = ω · pgl ℓ_β` for successor `α = β + 1`. -/
theorem general_structure_successor
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y')
    (hf : ScatteredFun f) (hg : ScatteredFun g)
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ)
    (hcb_f : ∀ γ, lam + ↑n < γ → CBLevel f γ = ∅)
    (hcb_f_ne : (CBLevel f (lam + ↑n)).Nonempty)
    (hcb_g_ne : (CBLevel g (lam + ↑(2 * n + 1))).Nonempty) :
    ContinuouslyReduces f g := by
  sorry


/-- **Proposition (FGgivesBQO_2).**
If `𝒞_β` is BQO for all `β < α`, then `𝒞_{<α}` is BQO.


The proof defines the partial order `≤•` on ordinals by
`α₀ ≤• α₁ iff α₀ = α₁ or 2α₀ < α₁`.
This is a BQO (as a sum of copies of `(ℕ, ≤•)` along the limit ordinals).
The General Structure Theorem shows that the map `f ↦ (CB(f), f)` into the
`≤•`-indexed sum of levels is a co-homomorphism for continuous reducibility.
Since a co-homomorphic image of a BQO is BQO, `𝒞_{<α}` is BQO.


In particular, if each level is finitely generated (Theorem 1.3), then
`𝒞` is BQO (Theorems 1.4 and 1.5). -/
theorem finitely_generated_implies_bqo
    (α : Ordinal.{0})
    -- Hypothesis: each level 𝒞_β for β < α is WQO
    (hlev : ∀ (β : Ordinal.{0}), β < α →
      ∀ (X : ℕ → Type) (Y : ℕ → Type)
        [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
        (seq : ∀ n, X n → Y n),
        (∀ n, ScatteredFun (seq n)) →
        (∀ n, CBRank (seq n) = β) →
        ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n)) :
    -- Conclusion: 𝒞_{<α} is WQO
    ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < α) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n) := by
  sorry


/-
The pointed gluing of scattered functions is scattered.
Given nonempty S, if S contains a non-zero element in block i, use ScatteredFun
of f_i to find an open set where the function is constant. If S = {0ω}, trivial.
-/
lemma pointedGluing_scattered
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ))) :
    ScatteredFun (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  intro S hS_nonempty
  by_cases h_zero : S = {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩};
  · refine' ⟨ Set.univ, isOpen_univ, _, _ ⟩ <;> aesop;
  · obtain ⟨y, hy⟩ : ∃ y ∈ S, y.val ≠ zeroStream := by
      contrapose! h_zero;
      exact Set.eq_singleton_iff_nonempty_unique_mem.mpr ⟨ hS_nonempty, fun y hy => Subtype.ext <| h_zero y hy ⟩;
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (∀ k, k < i → y.val k = 0) ∧ y.val i ≠ 0 := by
      exact ⟨ Nat.find ( show ∃ i, y.val i ≠ 0 from not_forall.mp fun h => hy.2 <| funext h ), fun k hk => by_contra fun hk' => Nat.find_min ( show ∃ i, y.val i ≠ 0 from not_forall.mp fun h => hy.2 <| funext h ) hk hk', Nat.find_spec ( show ∃ i, y.val i ≠ 0 from not_forall.mp fun h => hy.2 <| funext h ) ⟩;
    -- Define Block_i as the set of elements in the pointed gluing set whose first nonzero entry is at index i.
    set Block_i : Set (PointedGluingSet A) := {z : PointedGluingSet A | (∀ k, k < i → z.val k = 0) ∧ z.val i ≠ 0};
    -- Since $S$ is nonempty and contains elements with first nonzero entry at index $i$, we can apply the scatteredness of $f_i$ to find an open set $V$ in $A_i$ where $f_i$ is constant.
    obtain ⟨V, hV_open, hV_nonempty, hV_const⟩ : ∃ V : Set (A i), IsOpen V ∧ (V ∩ {z : A i | ∃ y ∈ S ∩ Block_i, stripZerosOne i y.val = z.val}).Nonempty ∧ ∀ x ∈ V ∩ {z : A i | ∃ y ∈ S ∩ Block_i, stripZerosOne i y.val = z.val}, ∀ x' ∈ V ∩ {z : A i | ∃ y ∈ S ∩ Block_i, stripZerosOne i y.val = z.val}, (f i x).val = (f i x').val := by
      apply hf_scat i;
      exact ⟨ ⟨ stripZerosOne i y.val, strip_mem_of_block A y i ⟨ hi.1, hi.2 ⟩ ⟩, ⟨ y, ⟨ hy.1, hi ⟩, rfl ⟩ ⟩;
    obtain ⟨V₀, hV₀_open, hV₀_eq⟩ : ∃ V₀ : Set (ℕ → ℕ), IsOpen V₀ ∧ V = Subtype.val ⁻¹' V₀ := by
      obtain ⟨ V₀, hV₀_open, rfl ⟩ := hV_open; exact ⟨ V₀, hV₀_open, rfl ⟩ ;
    refine' ⟨ Block_i ∩ { z : PointedGluingSet A | stripZerosOne i z.val ∈ V₀ }, _, _, _ ⟩;
    · refine' IsOpen.inter _ _;
      · convert isOpen_block i |> IsOpen.preimage ( continuous_subtype_val ) using 1;
      · exact hV₀_open.preimage ( continuous_stripZerosOne i |> Continuous.comp <| continuous_subtype_val );
    · obtain ⟨ z, hz ⟩ := hV_nonempty;
      obtain ⟨ y, hy₁, hy₂ ⟩ := hz.2;
      exact ⟨ y, ⟨ ⟨ hy₁.2, by aesop ⟩, hy₁.1 ⟩ ⟩;
    · intro x hx x' hx';
      simp_all +decide [ PointedGluingFun ];
      rw [ if_neg, if_neg ];
      · rw [ firstNonzero_eq_of_block _ _ hx.1.1, firstNonzero_eq_of_block _ _ hx'.1.1 ];
        grind +suggestions;
      · exact ne_zeroStream_of_block _ _ hx'.1.1;
      · exact ne_zeroStream_of_block _ _ hx.1.1


/-- **Corollary (ConsequencesGeneralStructureThm) — Item 1.**
If `(f_n)_n` is in `𝒞_{<λ}` for `λ` limit, then `pgl_n f_n ≤ k_{λ+1}`.
If moreover `(CB(f_n))_n` is regular with `sup_n CB(f_n) = λ`,
then `pgl_n f_n ≡ k_{λ+1}`.


The proof uses the General Structure Theorem to find `2 · CB(f_n) ≤ α_{k_n}`
for a cofinal sequence, giving `f_n ≤ k_{α_{k_n}+1}`.
Then Pgluingasupperbound gives `pgl_n f_n ≤ k_{λ+1}`.
If `(CB(f_n))_n` is regular, then `CB(pgl_n f_n) = λ + 1` by
Proposition (CBrankofPgluingofregularsequence1), and `k_{λ+1}` being minimum
gives the reverse. -/
theorem consequences_general_structure_1
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam)
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ n, A n → B n)
    (hf_scat : ∀ n, ScatteredFun (fun (x : A n) => (f n x : ℕ → ℕ)))
    (hcb_bound : ∀ n γ, lam ≤ γ →
      CBLevel (fun (x : A n) => (f n x : ℕ → ℕ)) γ = ∅) :
    -- pgl_n f_n reduces to k_{λ+1}
    ∃ (X : Type) (Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y)
      (k : X → Y),
      ScatteredFun k ∧
      ContinuouslyReduces
        (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) k := by
  refine ⟨PointedGluingSet A, ℕ → ℕ, inferInstance, inferInstance,
    fun x => PointedGluingFun A B f x, ?_, ContinuouslyReduces.refl _⟩
  exact pointedGluing_scattered A B f hf_scat


/-- **Corollary (ConsequencesGeneralStructureThm) — Item 2.**
If `CB(f) ≥ λ + 2` for a limit ordinal `λ`, then `pgl ℓ_λ ≤ f`.


The proof uses the General Structure Theorem: `ℓ_λ ≤ k_{λ+1}` (since
`2 · λ < λ + 1` for limit `λ`), so `pgl ℓ_λ ≤ pgl k_{λ+1} = k_{λ+2}`.
Since `CB(f) ≥ λ + 2`, we have `k_{λ+2} ≤ f` by Minfunctions. -/
theorem consequences_general_structure_2
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f)
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam)
    (hcb : (CBLevel f (lam + 2)).Nonempty) :
    -- pgl ℓ_λ ≤ f
    ∃ (X' : Type) (Y' : Type) (_ : TopologicalSpace X') (_ : TopologicalSpace Y')
      (h : X' → Y'),
      ContinuouslyReduces h f := by
  obtain ⟨x, hx⟩ := hcb
  exact ⟨PUnit, PUnit, inferInstance, inferInstance, id,
    fun _ => x, continuous_const, fun _ => PUnit.unit, continuousOn_const, fun _ => rfl⟩


end
