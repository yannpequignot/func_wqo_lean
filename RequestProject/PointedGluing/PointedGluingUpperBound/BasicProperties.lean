import RequestProject.PointedGluing.CBRankSimpleHelpers
import RequestProject.PointedGluing.ContinuousOnTau

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Pointed Gluing — Basic Properties (Fact 3.1, Proposition 3.2, Fact 3.3)

## Main results

* `pointedGluingFun_preserves_continuity` — Fact 3.1: preserves continuity
* `pointedGluingFun_preserves_injectivity` — Fact 3.1: preserves injectivity
* `pointedGluingFun_comm_id` — Fact 3.1: commutes with identity
* `zeroStream_continuity_point` — Fact 3.1: 0^ω is a continuity point
* `CBrank_pointedGluing_regular` — Proposition 3.2: CB rank of regular sequence
* `gluing_le_pointedGluing` — Fact 3.3: ⊔_i f_i ≤ pgl_i f_i
-/

noncomputable section

lemma strip_mem_of_pointedGluingSet (A : ℕ → Set (ℕ → ℕ))
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    stripZerosOne (firstNonzero x.val) x.val ∈ A (firstNonzero x.val) := by
  -- Since x ∈ PointedGluingSet A and x ≠ zeroStream, we can write x as prependZerosOne j a for some j and a ∈ A j.
  obtain ⟨j, a, ha₁, ha₂⟩ : ∃ j, ∃ a ∈ A j, (↑x : ℕ → ℕ) = prependZerosOne j a := by
    unfold PointedGluingSet at x; aesop
  unfold prependZerosOne at ha₂; simp_all +decide [ firstNonzero ] 
  convert ha₁ using 1
  · split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]
    · congr! 1
      rw [ Nat.find_eq_iff ] ; aesop
    · rename_i h; specialize h j le_rfl; aesop
  · convert stripZerosOne_prependZerosOne j a using 1
    congr! 1
    split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]
    rename_i h; specialize h j; aesop


/-
On a non-zero element, `PointedGluingFun` equals the block formula.
-/
lemma pointedGluingFun_eq_on_block (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i)
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    PointedGluingFun A B f x = prependZerosOne (firstNonzero x.val)
      (f (firstNonzero x.val) ⟨stripZerosOne (firstNonzero x.val) x.val,
        strip_mem_of_pointedGluingSet A x hx⟩).val := by
  unfold PointedGluingFun
  grind


/-
`stripZerosOne i` is continuous as a map `(ℕ → ℕ) → (ℕ → ℕ)`.
-/
lemma continuous_stripZerosOne (i : ℕ) : Continuous (stripZerosOne i) := by
  unfold stripZerosOne
  fun_prop


/-
The block set for index `i` (sequences starting with `i` zeros then a nonzero) is
open in `ℕ → ℕ`.
-/
lemma isOpen_block (i : ℕ) :
    IsOpen {x : ℕ → ℕ | (∀ k, k < i → x k = 0) ∧ x i ≠ 0} := by
  convert isOpen_pi_iff.mpr _
  intro f hf
  refine' ⟨Finset.range ( i + 1 ), fun k => if k < i then { 0 } else { x | x ≠ 0 }, _, _⟩ <;> simp_all +decide [ Set.subset_def ]
  · grind
  · grind


/-
`firstNonzero x = i` when `x` starts with `i` zeros and `x i ≠ 0`.
-/
lemma firstNonzero_eq_of_block (x : ℕ → ℕ) (i : ℕ)
    (h : (∀ k, k < i → x k = 0) ∧ x i ≠ 0) :
    firstNonzero x = i := by
  unfold firstNonzero
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
  convert strip_mem_of_pointedGluingSet A y _
  · exact Eq.symm ( firstNonzero_eq_of_block _ _ hy )
  · exact Eq.symm ( firstNonzero_eq_of_block _ _ hy )
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
  refine' continuous_pi_iff.2 fun j => _
  by_cases hj : j < i
  · exact continuous_const.congr fun x => by rw [ prependZerosOne, if_pos hj ] 
  · simp +decide [ prependZerosOne, hj ]
    by_cases h : j = i <;> simp_all +decide
    · exact continuous_const
    · exact continuous_apply _ |> Continuous.comp <| continuous_subtype_val.comp <| hf _ |> Continuous.comp <| Continuous.subtype_mk ( continuous_stripZerosOne _ |> Continuous.comp <| continuous_subtype_val.comp continuous_subtype_val ) _


/-
ContinuousAt of PointedGluingFun at a non-zero point.
-/
lemma continuousAt_pointedGluingFun_nonzero
    (A B : ℕ → Set (ℕ → ℕ)) (f : ∀ i, A i → B i) (hf : ∀ i, Continuous (f i))
    (x : PointedGluingSet A) (hx : x.val ≠ zeroStream) :
    ContinuousAt (fun y : PointedGluingSet A => PointedGluingFun A B f y) x := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (∀ k : ℕ, k < i → x.val k = 0) ∧ x.val i ≠ 0 := by
    exact ⟨Nat.find ( show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h ), fun k hk => by_contra fun hk' => Nat.find_min ( show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h ) hk <| by aesop, Nat.find_spec ( show ∃ i, x.val i ≠ 0 from not_forall.mp fun h => hx <| funext h )⟩
  have hV : IsOpen {y : PointedGluingSet A | (∀ k : ℕ, k < i → y.val k = 0) ∧ y.val i ≠ 0} := by
    exact isOpen_block i |> IsOpen.preimage ( continuous_subtype_val )
  have h_cont_restrict : ContinuousOn (fun y : PointedGluingSet A => PointedGluingFun A B f y) {y : PointedGluingSet A | (∀ k : ℕ, k < i → y.val k = 0) ∧ y.val i ≠ 0} := by
    rw [ continuousOn_iff_continuous_restrict ]
    refine' Continuous.congr _ _
    use fun y => prependZerosOne i ( f i ⟨stripZerosOne i y.val.val, strip_mem_of_block A y.val i y.prop⟩ ).val
    · exact continuous_block_restrict A B f hf i
    · intro y; ext; simp [PointedGluingFun]
      rw [ if_neg ( ne_zeroStream_of_block _ _ y.prop ) ]
      rw [ firstNonzero_eq_of_block _ _ y.2 ]
      grind
  exact h_cont_restrict.continuousAt ( hV.mem_nhds ⟨hi.1, hi.2⟩ )


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
        unfold PointedGluingFun
        split_ifs <;> simp_all +decide [ PointedGluingSet ]
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
  intro x y hxy
  by_cases hx : x.val = zeroStream <;> by_cases hy : y.val = zeroStream <;> simp_all +decide [ PointedGluingFun ]
  · aesop
  · -- Since $y \neq zeroStream$, we have $stripZerosOne (firstNonzero y) y \in A (firstNonzero y)$.
    obtain ⟨i, hi⟩ : ∃ i, y.val ∈ prependZerosOne i '' (A i) := by
      have := y.2
      cases this <;> aesop
    obtain ⟨z, hz, hz'⟩ := hi
    have h_firstNonzero : firstNonzero y.val = i := by
      unfold firstNonzero; simp +decide [ ← hz', prependZerosOne ] 
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]
      rename_i h; specialize h i; aesop
    specialize hxy (by
    grind +suggestions)
    replace hxy := congr_fun hxy i ; simp_all +decide [ zeroStream, prependZerosOne ]
  · have := hxy (by
    have hx_mem : x.val ∈ ⋃ i, prependZerosOne i '' (A i) := by
      exact Or.resolve_left x.2 hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx_mem
    generalize_proofs at *
    obtain ⟨a, ha, ha'⟩ := hi
    generalize_proofs at *
    rw [ ← ha' ]
    rw [ show firstNonzero ( prependZerosOne i a ) = i from ?_ ]
    · rw [ stripZerosOne_prependZerosOne ] ; assumption
    · unfold firstNonzero; simp +decide [ prependZerosOne ] 
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]
      rename_i h; specialize h i; aesop;)
    generalize_proofs at *
    replace this := congr_fun this ( firstNonzero x ) ; simp_all +decide [ prependZerosOne ] 
    exact absurd this ( by unfold zeroStream; norm_num )
  · -- Since $x$ and $y$ are not equal to the zero stream, we can apply the definition of `PointedGluingSet` to obtain that there exist $i$ and $j$ such that $x = \text{prependZerosOne } i z$ and $y = \text{prependZerosOne } j w$ for some $z \in A i$ and $w \in A j$.
    obtain ⟨i, z, hz⟩ : ∃ i z, x.val = prependZerosOne i z ∧ z ∈ A i := by
      have := x.2
      cases this <;> aesop
    obtain ⟨j, w, hw⟩ : ∃ j w, y.val = prependZerosOne j w ∧ w ∈ A j := by
      have := y.2
      cases this <;> aesop
    -- Since $x$ and $y$ are not equal to the zero stream, we have $firstNonzero x = i$ and $firstNonzero y = j$.
    have h_firstNonzero_x : firstNonzero x.val = i := by
      unfold firstNonzero
      split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]
      · unfold prependZerosOne; aesop
      · exact False.elim <| hx <| funext ‹_›
    have h_firstNonzero_y : firstNonzero y.val = j := by
      unfold firstNonzero
      split_ifs <;> simp_all +decide [ prependZerosOne ]
      · simp_all +decide [ Nat.find_eq_iff, prependZerosOne ]
      · rename_i h; specialize h j le_rfl; aesop
    by_cases hij : i = j <;> simp_all +decide [ prependZerosOne_injective ]
    · split_ifs at hxy <;> simp_all +decide [ prependZerosOne_injective ]
      · simp_all +decide [ Function.Injective.eq_iff ( prependZerosOne_injective j ) ]
        simp_all +decide [ stripZerosOne_prependZerosOne ]
        grind +revert
      · exact False.elim <| ‹stripZerosOne j ( prependZerosOne j w ) ∉ A j› <| by simpa [ stripZerosOne_prependZerosOne ] using hw.2
      · exact False.elim <| ‹stripZerosOne j ( prependZerosOne j z ) ∉ A j› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2
      · exact False.elim <| ‹stripZerosOne j ( prependZerosOne j z ) ∉ A j› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2
    · split_ifs at hxy <;> simp_all +decide [ prependZerosOne_injective ]
      · cases lt_or_gt_of_ne hij <;> have := congr_fun hxy ‹_› <;> simp_all +decide [ prependZerosOne ]
        have := congr_fun hxy i; simp_all +decide [ prependZerosOne ] 
      · simp_all +decide [ stripZerosOne_prependZerosOne ]
      · exact False.elim <| ‹stripZerosOne i ( prependZerosOne i z ) ∉ A i› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2
      · exact False.elim <| ‹stripZerosOne i ( prependZerosOne i z ) ∉ A i› <| by simpa [ stripZerosOne_prependZerosOne ] using hz.2


/-
**Fact (BasicsOnPointedGluing) — Part 3.**
Pointed gluing commutes with identity: `id_{pgl_i X_i} = pgl_i id_{X_i}`.
-/
theorem pointedGluingFun_comm_id (A : ℕ → Set (ℕ → ℕ)) :
    (fun x => PointedGluingFun A A (fun _i => id) x) =
    (fun (x : PointedGluingSet A) => x.val) := by
  unfold PointedGluingFun
  ext x
  split_ifs <;> simp_all +decide [ zeroStream, prependZerosOne ]
  have h_mem : ∃ i, ∃ x', x.val = prependZerosOne i x' ∧ x' ∈ A i := by
    rcases x with ⟨x, hx⟩
    cases hx <;> aesop
  obtain ⟨i, x', hx, hx'⟩ := h_mem
  rw [ show firstNonzero x.val = i from _ ]
  · simp +decide [ hx, stripZerosOne_prependZerosOne ]
    rw [ if_pos hx' ]
  · unfold firstNonzero
    split_ifs <;> simp_all +decide [ prependZerosOne ]
    · simp_all +decide [ Nat.find_eq_iff, prependZerosOne ]
    · rename_i h; specialize h i; aesop


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
  unfold PointedGluingFun
  refine' tendsto_pi_nhds.mpr _
  intro x
  simp [zeroStream]
  rw [ nhds_subtype_eq_comap ]
  refine' ⟨{ y : ℕ → ℕ | ∀ k < x + 1, y k = 0 }, _, _⟩ <;> norm_num [ zeroStream ]
  · rw [ nhds_pi ]
    simp +decide [ Filter.mem_pi, zeroStream ]
    exact ⟨Finset.range ( x + 1 ), Finset.finite_toSet _, fun _ => { 0 }, fun _ => by norm_num, fun y hy k hk => by simpa using hy k ( Finset.mem_range.mpr ( Nat.lt_succ_of_le hk ) )⟩
  · intro a ha h; split_ifs <;> simp_all +decide [ zeroStream ] 
    unfold firstNonzero
    split_ifs <;> simp_all +decide [ prependZerosOne ]
    exact False.elim <| ‹¬a = zeroStream› <| funext fun k => by aesop

lemma CBLevel_zero_ne_succ_of_scattered_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    CBLevel f 0 ≠ CBLevel f (Order.succ 0) := by
  intro h
  rw [ CBLevel_zero, CBLevel_succ' ] at h
  simp +decide [ Set.ext_iff ] at h
  contrapose! h
  exact Exists.elim ( scattered_isolatedLocus_nonempty f hf ( CBLevel f 0 ) ( by simp +decide [ CBLevel_zero ] ) ) fun x hx => ⟨x, fun _ => hx⟩

/-
For scattered functions on a Small.{0} type, the stabilization set for CBRank is nonempty.
-/
lemma CBRank_stabilization_set_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (_hne : Nonempty X) :
    {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty := by
  contrapose! hf
  obtain ⟨g, hg⟩ := CBLevel_strictAnti_of_ne f (by
  exact fun α => fun h => hf.subset h)
  exact False.elim ( not_injective_of_ordinal g hg )

/-
If f is scattered on a nonempty Small.{0} domain, then CBRank f > 0.
-/
lemma CBRank_pos_of_scattered_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (hne : Nonempty X) :
    CBRank f > 0 := by
  refine' pos_iff_ne_zero.mpr _
  have := CBLevel_zero_ne_succ_of_scattered_nonempty f hf hne
  exact fun h => this <| h ▸ csInf_mem ( CBRank_stabilization_set_nonempty f hf hne )

theorem emptyFun (A B : Set (ℕ → ℕ)) (f : A → B)
    (hf : ScatteredFun (fun x : A => (f x : ℕ → ℕ)))
    (h : CBRank (fun x : A => (f x : ℕ → ℕ)) = 0) : A = ∅ := by
  contrapose! h
  apply ne_of_gt
  apply CBRank_pos_of_scattered_nonempty
  · exact hf
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
  apply Set.eq_singleton_iff_unique_mem.mpr
  constructor
  · apply zeroStream_mem_CBLevel_le A B f hf_scat cbranks hreg hα α hαsup hαpos α (le_refl α)
  · apply CBLevel_pointedGluing_subset
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
    exact ⟨i, by simp [ prependZerosOne, zeroStream ]⟩
  exact fun h => h_neq.choose_spec <| congr_fun h _


theorem firstNonzero_prependZerosOne (i : ℕ) (x : ℕ → ℕ) :
    firstNonzero (prependZerosOne i x) = i := by
  unfold firstNonzero
  split_ifs <;> simp_all +decide [ Nat.find_eq_iff ]
  · unfold prependZerosOne; aesop
  · rename_i h; specialize h i; simp_all +decide [ prependZerosOne ] 


theorem continuous_prependZerosOne (i : ℕ) : Continuous (prependZerosOne i) := by
  refine' continuous_pi fun n => _
  unfold prependZerosOne
  split_ifs <;> continuity


theorem gluing_le_pointedGluing
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i) :
    ContinuouslyReduces
      (fun (x : GluingSet A) => GluingFunVal A B f x)
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  -- The σ function is continuous because it is a composition of continuous functions.
  have hσ_cont : Continuous (gluingToPointed A) := by
    refine' continuous_induced_rng.mpr _
    -- The function x ↦ prependZerosOne (x.val 0) (unprepend x.val) is continuous because it is a composition of continuous functions.
    have h_cont : ∀ n, ContinuousOn (fun x : GluingSet A => prependZerosOne n (unprepend x.val)) {x : GluingSet A | x.val 0 = n} := by
      intro n
      have h_cont : Continuous (fun x : ℕ → ℕ => prependZerosOne n (unprepend x)) := by
        exact continuous_pi_iff.mpr fun i => by cases i <;> continuity
      generalize_proofs at *; (
      exact h_cont.comp_continuousOn ( continuous_subtype_val.continuousOn ))
    refine' continuous_iff_continuousAt.mpr _
    intro x
    have h_cont_at : ContinuousAt (fun x : GluingSet A => prependZerosOne (x.val 0) (unprepend x.val)) x := by
      have h_cont_at : ∀ᶠ y in nhds x, y.val 0 = x.val 0 := by
        have h_cont_at : IsOpen {y : GluingSet A | y.val 0 = x.val 0} := by
          have h_cont_at : IsOpen {y : ℕ → ℕ | y 0 = x.val 0} := by
            rw [ isOpen_pi_iff ]
            exact fun f hf => ⟨{ 0 }, fun _ => { y | y = x.val 0 }, by aesop⟩
          generalize_proofs at *
          exact h_cont_at.preimage ( continuous_subtype_val )
        generalize_proofs at *
        exact h_cont_at.mem_nhds rfl
      generalize_proofs at *
      exact ContinuousAt.congr ( h_cont ( x.val 0 ) |> ContinuousOn.continuousAt <| by filter_upwards [ h_cont_at ] with y hy; aesop ) <| Filter.eventuallyEq_of_mem h_cont_at fun y hy => by aesop
    generalize_proofs at *
    convert h_cont_at using 1
    generalize_proofs at *
    grind +locals
  refine' ⟨gluingToPointed A, hσ_cont, pointedToGluing, _, _⟩
  · -- Since the range of the composition is a subset of the set where pointedToGluing is continuous, we can conclude that pointedToGluing is continuous on the range.
    have h_range_subset : Set.range ((fun x => PointedGluingFun A B f x) ∘ gluingToPointed A) ⊆ {y | y ≠ zeroStream} := by
      intro y hy; obtain ⟨x, rfl⟩ := hy; simp +decide [ PointedGluingFun ] 
      unfold gluingToPointed; simp +decide [ prependZerosOne_ne_zeroStream ] 
      rw [ firstNonzero_prependZerosOne ]
      convert ( GluingSet_inverse_short A x ).choose_spec.2 using 1
      exact stripZerosOne_prependZerosOne _ _
    refine' ContinuousOn.mono _ h_range_subset
    -- The function pointedToGluing is continuous on the set where y is not zeroStream because it is a composition of continuous functions.
    have h_cont : ContinuousOn (fun y => prepend (firstNonzero y) (stripZerosOne (firstNonzero y) y)) {y | y ≠ zeroStream} := by
      -- Since `firstNonzero` is locally constant on `{y | y ≠ zeroStream}`, we can use the fact that the composition of continuous functions is continuous.
      have h_locally_const : ∀ y : ℕ → ℕ, y ≠ zeroStream → ∃ U : Set (ℕ → ℕ), IsOpen U ∧ y ∈ U ∧ ∀ z ∈ U, firstNonzero z = firstNonzero y := by
        intro y hy
        use {z | z (firstNonzero y) ≠ 0 ∧ ∀ n < firstNonzero y, z n = 0}
        refine' ⟨_, _, _⟩
        · simp +decide only [setOf_and, setOf_forall]
          refine' IsOpen.inter _ _
          · exact isOpen_ne.preimage ( continuous_apply _ )
          · refine' isOpen_iff_forall_mem_open.mpr _
            intro x hx
            refine' ⟨⋂ i ∈ Finset.range ( firstNonzero y ), { z : ℕ → ℕ | z i = 0 }, _, _, _⟩ <;> simp_all +decide [ Set.subset_def ]
            rw [ show ( ⋂ i, ⋂ ( _ : i < firstNonzero y ), { z : ℕ → ℕ | z i = 0 } ) = ⋂ i ∈ Finset.range ( firstNonzero y ), { z : ℕ → ℕ | z i = 0 } by ext; aesop ] ; exact isOpen_biInter_finset fun i hi => isOpen_discrete { 0 } |> IsOpen.preimage ( continuous_apply i ) 
        · unfold firstNonzero
          split_ifs <;> simp_all +decide [ zeroStream ]
          · exact Nat.find_spec ‹∃ k, y k ≠ 0›
          · exact hy ( funext ‹_› )
        · intro z hz
          refine' le_antisymm _ _ <;> simp_all +decide [ firstNonzero ]
          · split_ifs at * <;> simp_all +decide [ Nat.find_eq_iff ]
            grind +suggestions
          · split_ifs at * <;> simp_all +decide [ Nat.find_eq_iff ]
      intro y hy
      obtain ⟨U, hU_open, hyU, hU_const⟩ := h_locally_const y hy
      have h_cont_on_U : ContinuousOn (fun z => prepend (firstNonzero y) (stripZerosOne (firstNonzero y) z)) U := by
        refine' Continuous.continuousOn _
        exact continuous_prepend _ |> Continuous.comp <| continuous_pi fun _ => continuous_apply _
      generalize_proofs at *
      exact ContinuousAt.continuousWithinAt ( by exact ContinuousAt.congr ( h_cont_on_U.continuousAt ( hU_open.mem_nhds hyU ) ) ( Filter.eventuallyEq_of_mem ( hU_open.mem_nhds hyU ) fun z hz => by aesop ) )
    refine' h_cont.congr fun y hy => _
    unfold pointedToGluing; aesop
  · unfold GluingFunVal pointedToGluing PointedGluingFun gluingToPointed
    grind +suggestions

