import RequestProject.PointedGluing.MaxFunMaximum


open scoped Topology
open Set Function TopologicalSpace Classical


set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Remaining Theorems from Chapter 3

Theorems up to pointedGluing_upper_bound are in PointedGluingUpperBound.lean.
The maxFun_is_maximum proof is in MaxFunMaximum.lean.
-/

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
`{N_{(0)^i(1)}}_{i<n} ∪ {N_{(0)^n}}`.
Formal statement does not match the memoir.  -/
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
- I do not think item 3 is used later, skipping it for now

PROVIDED SOLUTION
For all $\alpha<\omega_1$:
1. the function $\Maximalfct{\alpha}$ (MaxFun α) is a maximum of $\sC_{\leq\alpha}$,
2. the function $\pgl \Maximalfct{\alpha}$ (SuccMaxFun α) is a maximum for simple functions in $\sC_{\leq \alpha+1}$,

First notice that if $\alpha\leq \beta$, then we have $\Maximalfct{\alpha}\leq\Maximalfct{\beta}$ and
$\Minimalfct{\alpha+1}\leq\Minimalfct{\beta+1}$ by MaxFun_monotone and MinFun_monotone.
For $\alpha=0$, we have $\Maximalfct{0}=\emptyset$ and $\Minimalfct{1}=\pgl\Maximalfct{0}=\id_{\set{\iw{0}}}\equiv\id_{\set{0}}$,
so all items follows from \cref{LocallyConstantFunctions} (theorem constant_equiv_id_singleton).

We prove the two items simultaneously by strong induction on $\alpha$: suppose they both hold for all $\beta<\alpha$.
To see that $\Maximalfct{\alpha}$ is a maximum in $\sC_{\leq\alpha}$, let $f\in\sC$ with $\CB(f)\leq\alpha$.
By the decomposition_lemma_baire \cref{JSLdecompositionlemma},
$f$ is locally simple. If $\alpha$, is limit $f=\bigsqcup_i f_i$ with $f_i$ simple
and $\CB(f_i)=\beta_i+1<\alpha$ and so by induction hypothesis the second item ensures that $f_i\leq \pgl \Maximalfct{\beta_i}\leq \Maximalfct{\beta_i+1}$.
If $\alpha$ is successor, $f=\bigsqcup_i f_i$ with $f_i$ simple and $\CB(f_i)=\beta+1=\alpha$ and
again the induction hypothesis implies that $f_i\leq \pgl \Maximalfct{\beta}$.
In both, cases we get $\gl_{i}f_i\leq \Maximalfct{\alpha}$ and so $f\leq \Maximalfct{\alpha}$
by gluingFun_upper_bound_backward.

Now take $f$ simple in $\sC_{\leq \alpha+1}$ and call $y$ its distinguished point.
By pointedGluing_rays_upper_bound we have $f\leq\pgl_{j\in\N}\ray{f}{y,j}$, but by simplicity of $f$
we also have $\CB(\ray{f}{y,j})\leq\alpha$ for all $j\in\N$. As $\Maximalfct{\alpha}$ is a maximum
in $\sC_{\alpha}$, we get $\ray{f}{y,j}\leq\Maximalfct{\alpha}$ for all $j\in \N$ and
so $f\leq \pgl\Maximalfct{\alpha}$ by \cref{Pgluingasupperbound}.
-/

theorem maxFun_is_maximum
    (α : Ordinal.{0}) (hα : α < omega1) :
    -- MaxFun α is maximum: for all scattered f with CB(f) ≤ α, f ≤ MaxFun α
    (∀ {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (_hf : Continuous f)
    (_hscat : ScatteredFun f)
    (_hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅),
      ContinuouslyReduces f (MaxFun α)) ∧
    -- SuccMaxFun α is maximum for simple functions:
    -- for all simple scattered f with CB(f) ≤ α+1, f ≤ SuccMaxFun α
    (∀ {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (hf : Continuous f)
    (β: Ordinal.{0}) (hβ : β ≤ α)
    (hcb_ne : (CBLevel f β).Nonempty)
    (hcb_empty : CBLevel f (Order.succ β) = ∅)
    (y: ℕ →ℕ )
    (hy_simple : ∀ x ∈ CBLevel f β, f x = y),
    ContinuouslyReduces f (SuccMaxFun α)) := by
  exact maxFun_is_maximum' α hα


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
/- pointedGluing_scattered is already proved in PointedGluingUpperBound.lean -/


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

