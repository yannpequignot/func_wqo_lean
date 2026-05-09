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

theorem pointedGluing_lower_bound
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
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
  -- Build the sequence (σ n, τ n) with data (k n, l n, m n)
  -- Using explicit recursion via Nat.rec to preserve the cross-step
  -- invariant kseq (n+1) = lseq n.
  -- ----------------------------------------------------------------
  have cyl_antitone : ∀ m n : ℕ, m ≤ n → cyl n ⊆ cyl m := by
    intro m n hmn a ha i hi
    exact ha i (Finset.range_mono hmn hi)
  -- Step function: given n and prevl (= kseq n), produce (l, m, σ, τ)
  -- with l ≥ prevl + 1, σ mapping into cyl prevl, etc.
  have mkStep : ∀ (n : ℕ) (prevl : ℕ), ∃ (l m : ℕ) (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      l ≥ prevl + 1 ∧
      Continuous σ ∧
      (∀ z, (g n z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ cyl prevl) ∧
      closure (Set.range (fun z => f (σ z))) ∩ cylfx m = ∅ ∧
      (∀ a ∈ cyl l, f a ∈ cylfx m) := by
    intro n prevl
    obtain ⟨σ, τ, hσc, hcomm, hτc, hσU, hclos⟩ :=
      hloc n (cyl prevl) (hcyl_open prevl) (hx_cyl prevl)
    obtain ⟨m, hm⟩ := find_m _ hclos
    obtain ⟨l₀, hl₀⟩ := find_l m
    exact ⟨max l₀ (prevl + 1), m, σ, τ, le_max_right _ _, hσc, hcomm, hτc, hσU, hm,
      fun a ha => hl₀ a (fun i hi => ha i (Finset.range_mono (le_max_left _ _) hi))⟩
  -- Build kseq (= prevl values) by explicit Nat.rec:
  --   kseq 0 = 0
  --   kseq (n+1) = l from step n = (mkStep n (kseq n)).choose
  let kseq : ℕ → ℕ := Nat.rec 0 (fun n prev => (mkStep n prev).choose)
  -- lseq n = kseq (n+1) = the l output from step n
  let lseq : ℕ → ℕ := fun n => kseq (n + 1)
  -- Extract step data via choose from mkStep n (kseq n)
  -- Note: lseq n = kseq (n+1) = (mkStep n (kseq n)).choose by definition
  have stepSpec : ∀ n, ∃ (m : ℕ) (σ : C n → A) (τ : (ℕ → ℕ) → ℕ → ℕ),
      lseq n ≥ kseq n + 1 ∧
      Continuous σ ∧
      (∀ z, (g n z : ℕ → ℕ) = τ (f (σ z))) ∧
      ContinuousOn τ (Set.range (fun z => f (σ z))) ∧
      (∀ z, σ z ∈ cyl (kseq n)) ∧
      closure (Set.range (fun z => f (σ z))) ∩ cylfx m = ∅ ∧
      (∀ a ∈ cyl (lseq n), f a ∈ cylfx m) := by
    intro n
    exact (mkStep n (kseq n)).choose_spec
  choose mseq σseq τseq hstep using stepSpec
  -- Unpack properties
  have hl    : ∀ n, lseq n ≥ kseq n + 1         := fun n => (hstep n).1
  have hσc   : ∀ n, Continuous (σseq n)          := fun n => (hstep n).2.1
  have hcomm : ∀ n z, (g n z : ℕ → ℕ) = τseq n (f (σseq n z)) :=
                                                     fun n => (hstep n).2.2.1
  have hτc   : ∀ n, ContinuousOn (τseq n)
      (Set.range (fun z => f (σseq n z)))         := fun n => (hstep n).2.2.2.1
  have hσcyl : ∀ n z, σseq n z ∈ cyl (kseq n)   := fun n => (hstep n).2.2.2.2.1
  have hclos : ∀ n, closure (Set.range (fun z => f (σseq n z))) ∩
      cylfx (mseq n) = ∅                         := fun n => (hstep n).2.2.2.2.2.1
  have hfl   : ∀ n a, a ∈ cyl (lseq n) → f a ∈ cylfx (mseq n) :=
                                                     fun n => (hstep n).2.2.2.2.2.2
  -- Key monotonicity: kseq is strictly increasing
  have kseq_strictMono : StrictMono kseq := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le le_rfl) (hl n)
  -- kseq n ≥ n
  have hk : ∀ n, kseq n ≥ n := by
    intro n; induction n with
    | zero => simp [kseq]
    | succ n ih =>
      -- kseq (n+1) = lseq n ≥ kseq n + 1 ≥ n + 1
      show lseq n ≥ n + 1
      calc lseq n ≥ kseq n + 1 := hl n
        _ ≥ n + 1 := Nat.add_le_add_right ih 1
  -- ----------------------------------------------------------------
  -- The threading lemma: f(σseq q z) ∈ cylfx (mseq p) for all q > p
  -- ----------------------------------------------------------------
  have threading : ∀ p q : ℕ, p < q → ∀ z, f (σseq q z) ∈ cylfx (mseq p) := by
    intro p q hpq z
    apply hfl p
    apply cyl_antitone (lseq p) (kseq q)
    · -- lseq p = kseq (p+1) ≤ kseq q since kseq is strictly mono and p+1 ≤ q
      exact kseq_strictMono.monotone hpq
    · exact hσcyl q z
  -- ----------------------------------------------------------------
  -- Define An and apply pointedGluing_lower_bound_lemma
  -- ----------------------------------------------------------------
  let An : ℕ → Set A := fun n => Set.range (σseq n)
  let σ_n : ∀ n, C n → An n := fun n z => ⟨σseq n z, Set.mem_range_self z⟩
  apply pointedGluing_lower_bound_lemma f hf C D g x An
  · -- hsep: ∀ n, f x ∉ closure (f '' An n)
    intro n
    -- f '' An n = range (f ∘ σseq n)
    -- hclos n says closure(range(f ∘ σseq n)) ∩ cylfx (mseq n) = ∅
    -- hfx_cylfx says f x ∈ cylfx (mseq n)
    -- So f x ∉ closure(range(f ∘ σseq n)) = closure(f '' An n)
    -- Since $f x \in \text{cylfx } (mseq n)$ and $\text{closure } (\text{range } (f \circ \sigmaseq n)) \cap \text{cylfx } (mseq n) = \emptyset$, it follows that $f x \notin \text{closure } (\text{range } (f \circ \sigmaseq n))$.
    have h_not_in_closure : f x ∉ closure (range (fun z => f (σseq n z))) := by
      exact fun h => Set.notMem_empty _ <| hclos n ▸ Set.mem_inter h ( hfx_cylfx _ );
    convert h_not_in_closure using 1;
    simp +decide [ An, Set.image ];
    congr! 2;
    exact Set.ext fun x => ⟨ by rintro ⟨ a, ha, ⟨ b, hb, hab ⟩, rfl ⟩ ; exact ⟨ ⟨ b, hb ⟩, by simp [ hab ] ⟩, by rintro ⟨ ⟨ a, ha ⟩, rfl ⟩ ; exact ⟨ _, _, ⟨ a, ha, rfl ⟩, rfl ⟩ ⟩
  · -- hrelclop: IsRelativeClopenPartition (fun m => f '' An m)
    constructor;
    · intro i j hij;
      -- Since $i \neq j$, without loss of generality, assume $i < j$.
      wlog hij : i < j generalizing i j;
      · exact Disjoint.symm ( this _ _ ( Ne.symm ‹_› ) ( lt_of_le_of_ne ( le_of_not_gt hij ) ( Ne.symm ‹_› ) ) );
      · have h_disjoint : f '' An j ⊆ cylfx (mseq i) := by
          exact Set.image_subset_iff.mpr fun z hz => by obtain ⟨ w, rfl ⟩ := hz; exact threading i j hij w;
        have h_disjoint : f '' An i ⊆ closure (range (fun z => f (σseq i z))) := by
          exact Set.image_subset_iff.mpr fun x hx => subset_closure <| by obtain ⟨ z, rfl ⟩ := hx; exact Set.mem_range_self z;
        exact Set.disjoint_left.mpr fun x hx₁ hx₂ => Set.notMem_empty x <| hclos i ▸ Set.mem_inter ( h_disjoint hx₁ ) ( ‹f '' An j ⊆ cylfx ( mseq i ) › hx₂ );
    · intro n;
      -- Let's define the clopen set C_n.
      set C_n := (cylfx (mseq n))ᶜ ∩ ⋂ m ∈ Finset.range n, cylfx (mseq m);
      -- By definition of $C_n$, we know that $f '' An n \subseteq C_n$.
      have h_subset : ∀ z ∈ An n, f z ∈ C_n := by
        rintro _ ⟨ z, rfl ⟩;
        refine' ⟨ _, _ ⟩;
        · exact fun h => hclos n |> fun h' => h' |> fun h'' => h'' |> fun h''' => h''' |> fun h'''' => h'''' |> fun h''''' => h''''' |> fun h'''''' => h'''''' |> fun h''''''' => h''''''' |> fun h'''''''' => by
            exact h'''''''' |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => h |> fun h => by
              have := h
              exact this.subset ⟨ subset_closure ⟨ z, rfl ⟩, by assumption ⟩;
        · exact Set.mem_iInter₂.mpr fun m hm => threading m n ( Finset.mem_range.mp hm ) z;
      -- By definition of $C_n$, we know that $f '' An j \cap C_n = \emptyset$ for $j \neq n$.
      have h_disjoint : ∀ j, j ≠ n → ∀ z ∈ An j, f z ∉ C_n := by
        intros j hj z hz hC_n
        by_cases h_cases : j < n;
        · obtain ⟨ w, rfl ⟩ := hz;
          exact hclos j |> fun h => h.subset ⟨ subset_closure <| Set.mem_range_self w, hC_n.2 |> Set.mem_iInter₂.mp |> fun h => h j ( Finset.mem_range.mpr h_cases ) ⟩;
        · grind;
      -- Since $C_n$ is clopen, the preimage of $C_n$ under the inclusion map is open.
      have h_preimage_open : IsOpen (Subtype.val ⁻¹' C_n : Set (⋃ j, f '' An j)) := by
        refine' IsOpen.preimage _ _;
        · exact continuous_subtype_val;
        · exact IsOpen.inter ( isOpen_compl_iff.mpr ( hcylfx_clopen _ |>.1 ) ) ( isOpen_biInter_finset fun _ _ => hcylfx_open _ );
      convert h_preimage_open using 1;
      ext ⟨z, hz⟩; simp;
      constructor;
      · rintro ⟨ a, ha, ha', rfl ⟩ ; exact h_subset _ ha';
      · obtain ⟨ j, hj ⟩ := Set.mem_iUnion.mp hz;
        grind
  · -- hconv: SetsConvergeTo An x
    intro U hU hxU
    obtain ⟨m₀, hm₀⟩ := hbasis_x U hU hxU
    exact ⟨m₀, fun n hn a ha => by
      obtain ⟨z, rfl⟩ := ha
      exact hm₀ (cyl_antitone m₀ (kseq n) (le_trans hn (hk n)) (hσcyl n z))⟩
  · -- hred: ContinuouslyReduces (g n) (f ∘ Subtype.val)
    intro n
    refine ⟨σ_n n, (hσc n).subtype_mk _, τseq n, ?_, fun z => hcomm n z⟩
    convert hτc n using 2

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
  -- -- Pick x ∈ CBLevel f α as the base point for pointedGluing_lower_bound
  -- obtain ⟨x, hx⟩ := hlevel_ne
  -- -- MinFun α is a pointed gluing, so apply the lower bound criterion
  -- -- The index type for the pointed gluing depends on whether α is successor or limit:
  -- --   α = β+1: MinFun (β+1) = ptgl (MinFun β), index type = ℕ (constant sequence)
  -- --   α limit: MinFun α = ptgl_n (MinFun αₙ), for (αₙ) cofinal in α
  -- apply pointedGluing_lower_bound f hf C D g x
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
  --   -- Now produce (σ, τ) from h_ih satisfying the pointedGluing_lower_bound conditions
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
    (α : Ordinal.{0}) (hα : α < omega1)
    (A : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hne : (CBLevel f α).Nonempty) :  -- this implies CBRank f > α+1
        ContinuouslyReduces (MinFun α) f := by
  sorry
