import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs

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

/-- `ω₁` as a countable ordinal. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord

/-!
## Section 1: Basic Properties of Pointed Gluing (Fact 3.1, Proposition 3.2, Fact 3.3)
-/

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
  sorry

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

/-- **Proposition (CBrankofPgluingofregularsequence1).**
Let `f = pgl_{n ∈ ℕ} f_n` for a sequence of scattered functions in 𝒞.
If `(CB(f_n))_n` is regular with supremum `α`, then `CB_α(f) = {0^ω}`.
In particular, `f` is simple with distinguished point `0^ω` and `CB(f) = α + 1`.

The proof uses: since `f_n ≡ f|_{N_{(0)^n(1)}}`, we have `CB(f_n) = CB(f|_{N_{(0)^n(1)}})`.
If `β < α`, then by regularity, `CB_β(f) ∩ N_{(0)^n(1)}` is nonempty for infinitely
many `n`, which implies `0^ω ∈ CB_{β+1}(f)`. Therefore `0^ω ∈ CB_α(f)`.
Since `CB_α(f|_{N_{(0)^n(1)}}) = ∅` for all `n`, we get `CB_α(f) = {0^ω}`. -/
theorem CBrank_pointedGluing_regular
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_scat : ∀ i, ScatteredFun (fun (x : A i) => (f i x : ℕ → ℕ)))
    (cbranks : ℕ → Ordinal.{0})
    (hreg : IsRegularOrdSeq cbranks)
    (hα : ∀ i, CBRank (fun (x : A i) => (f i x : ℕ → ℕ)) = cbranks i)
    (α : Ordinal.{0}) (hαsup : α = ⨆ n, cbranks n) :
    CBLevel (fun (x : PointedGluingSet A) => (PointedGluingFun A B f x : ℕ → ℕ)) α =
      {⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩} := by
  sorry

/-- **Fact (GluinglowerthanPgluing).**
Given a sequence `(f_i)_i` in 𝒞, we have `⊔_i f_i ≤ pgl_i f_i`.

The proof uses Gluingaslowerbound with `f = pgl_i f_i` and
`B_i = N_{(0)^i(1)}`. -/
theorem gluing_le_pointedGluing
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i) :
    ContinuouslyReduces
      (fun (x : GluingSet A) => GluingFunVal A B f x)
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x) := by
  sorry

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
              (fun a => ⟨a.val, by sorry⟩)
            else fun a => ⟨a.val, by sorry⟩) x)) :
    ContinuouslyReduces f
      (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  sorry

/-- **Corollary (Pgluingofraysasupperbound).**
For any continuous `f : A → B` in 𝒞 and any `y ∈ B`,
`f ≤ pgl_{i ∈ ℕ} Ray(f, y, i)`.

This is a direct application of Pgluingasupperbound with the identity partition
`I_j = {j}`. -/
theorem pointedGluing_rays_upper_bound
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (y : ℕ → ℕ) (hy : y ∈ B) :
    ∃ (C D : ℕ → Set (ℕ → ℕ)) (h : ∀ i, C i → D i),
      ContinuouslyReduces f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D h x) := by
  sorry

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
`CB(f) = α + 1`. -/
theorem CBrank_regular_simple
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf_scat : ScatteredFun f)
    (α : Ordinal.{0})
    (hcb_ne : (CBLevel f α).Nonempty)
    (hcb_empty : CBLevel f (Order.succ α) = ∅)
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (ray_cb : ℕ → Ordinal.{0})
    (hray_cb : ∀ n, ray_cb n = CBRank
      (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val)) :
    IsRegularOrdSeq ray_cb ∧ ⨆ n, ray_cb n = α := by
  sorry

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
- For the third item, induction on `n` using the compact domain structure. -/
theorem maxFun_is_maximum
    (α : Ordinal.{0}) (hα : α < omega1) :
    -- There exists a function ℓ_α that is maximum in 𝒞_{≤α}
    ∃ (X : Type) (Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y)
      (maxf : X → Y),
      -- maxf is scattered with CB(maxf) ≤ α
      ScatteredFun maxf ∧
      (∀ β : Ordinal.{0}, α < β → CBLevel maxf β = ∅) ∧
      -- maxf is maximum: for all scattered f with CB(f) ≤ α, f ≤ maxf
      (∀ (X' : Type) (Y' : Type) (_ : TopologicalSpace X') (_ : TopologicalSpace Y')
        (f : X' → Y'),
        ScatteredFun f → (∀ β : Ordinal.{0}, α < β → CBLevel f β = ∅) →
        ContinuouslyReduces f maxf) := by
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
    -- There exists a function k_{α+1} that is minimum in 𝒞_{≥α+1}
    ∃ (X : Type) (Y : Type) (_ : TopologicalSpace X) (_ : TopologicalSpace Y)
      (minf : X → Y),
      -- minf is scattered with CB(minf) = α + 1
      ScatteredFun minf ∧
      (CBLevel minf (Order.succ α)).Nonempty ∧
      CBLevel minf (Order.succ (Order.succ α)) = ∅ ∧
      -- minf is minimum: for all f with CB(f) ≥ α + 1, minf ≤ f
      (∀ (X' : Type) (Y' : Type) (_ : TopologicalSpace X') (_ : TopologicalSpace Y')
        (f : X' → Y'),
        ScatteredFun f → (CBLevel f (Order.succ α)).Nonempty →
        ContinuouslyReduces minf f) := by
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
  sorry

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
  sorry

end