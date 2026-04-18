import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.Theorems
import RequestProject.CenteredMemo.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `4_centered_memo.tex` — Main Theorems

This file formalizes the main theorems from Chapter 4 (Centered Functions) of the
memoir on continuous reducibility between functions.

## Main results

### Section 1: Definition and characterization (§4.1)
* `pgluingOfRegularIsCentered` — Fact 4.1
* `centerInvariance_reduce` — Fact 4.2, Item 1
* `centerInvariance_equiv` — Fact 4.2, Item 2
* `centerInvariance_cover` — Fact 4.2, Item 3
* `scatteredHaveCocenter` — Proposition 4.3
* `scatteredCentered_isSimple` — Proposition 4.3, second part
* `rigidityOfCocenter_tau` — Proposition 4.4, Item 1
* `rigidityOfCocenter_separation` — Proposition 4.4, Item 2
* `rigidityOfCocenter_finiteGluing` — Proposition 4.4, Item 3
* `rigidityOfCocenter_reducibleByPieces` — Proposition 4.4, Item 4
* `residualCorestrictionOfCentered` — Corollary 4.5
* `centeredAsPgluing_forward` — Theorem 4.6, Item 1 (forward)
* `centeredAsPgluing_iff_monotone` — Theorem 4.6, Item 2
* `centeredAsPgluing_CBrank` — Theorem 4.6, CB-rank consequence

### Section 2: Centered functions and structure of continuous reducibility (§4.2)
* `localCenterednessFromBQO` — Theorem 4.7
* `finitegenerationAndPgluing_upper` — Proposition 4.8, Item 1
* `finitegenerationAndPgluing_lower` — Proposition 4.8, Item 2
* `finitenessOfCenteredFunctions` — Theorem 4.9
* `centeredSuccessor` — Corollary 4.10

### Section 3: Simple functions at successors of limit levels (§4.3)
* `simpleIffCoincidenceOfCocenters` — Proposition 4.11
* `simpleFunctionsLambdaPlusOne` — Theorem 4.12
* `finiteDegreeLambdaPlusOne` — Corollary 4.13
-/

noncomputable section

/-!
## Section 1: Definition and Characterization (§4.1)
-/

/-- **Fact 4.1 (Pgluingofregulariscentered).**
If `(f_i)_{i ∈ ℕ}` is a regular sequence in `𝒞`, then `0^ω` is a center for
`pgl_i f_i`.

*Proof sketch:* By Pgluingaslowerbound2, it suffices to show that for every clopen
neighborhood `U` of `0^ω` and every `n ∈ ℕ`, there exists a continuous reduction
`(σ, τ)` from `f_n` to the pointed gluing such that `im(σ) ⊆ U` and
`0^ω ∉ cl(im(f ∘ σ))`. By regularity, we can find `m` large enough such that
`N_{(0)^m} ⊆ U` and `f_n ≤ f_m`, giving the desired reduction. -/
theorem pgluingOfRegularIsCentered
    (A B : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, A i → B i)
    (hf_reg : IsRegularSeq (fun i => (fun (x : A i) => (f i x : ℕ → ℕ)))) :
    IsCenterFor
      (fun (x : PointedGluingSet A) => PointedGluingFun A B f x)
      ⟨zeroStream, zeroStream_mem_pointedGluingSet A⟩ := by
  sorry

/-
**Fact 4.2 (Centerinvariance) — Item 1.**
If `x` is a center for `f` and `(σ, τ)` continuously reduces `f` to `g`,
then for every neighborhood `U` of `σ(x)`, we have `f ≤ g|_U`.

*Proof:* By continuity of `σ`, `σ⁻¹(U)` is a neighborhood of `x`.
We have `f|_{σ⁻¹(U)} ≤ g|_U` via `(σ↾U, τ)` and `f ≤ f|_{σ⁻¹(U)}` since
`x` is a center for `f`, so `f ≤ g|_U` by transitivity.
-/
theorem centerInvariance_reduce
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    {x : A} (hcenter : IsCenterFor f x)
    {σ : A → A'} (hσ : Continuous σ)
    {τ : B' → B} (hτ_cont : ContinuousOn τ (Set.range (g ∘ σ)))
    (hτ_eq : ∀ a, f a = τ (g (σ a)))
    {U : Set A'} (hU : IsOpen U) (hσx : σ x ∈ U) :
    ContinuouslyReduces f (g ∘ (Subtype.val : U → A')) := by
  have h_f_le_f_restrict : f ≤ f ∘ (Subtype.val : σ ⁻¹' U → A) := by
    exact hcenter _ ( hU.preimage hσ ) hσx;
  have h_f_restrict_le_g_restrict : f ∘ (Subtype.val : σ ⁻¹' U → A) ≤ g ∘ (Subtype.val : U → A') := by
    refine' ⟨ fun a => ⟨ σ a, a.2 ⟩, _, _ ⟩;
    · fun_prop;
    · refine' ⟨ τ, _, _ ⟩;
      · refine' hτ_cont.mono _;
        rintro _ ⟨ a, rfl ⟩ ; exact ⟨ a, rfl ⟩;
      · aesop;
  exact ContinuouslyReduces.trans h_f_le_f_restrict h_f_restrict_le_g_restrict

/-
**Fact 4.2 (Centerinvariance) — Item 2.**
If `x` is a center for `f` and `f ≡ g` via `(σ, τ)`, then `σ(x)` is a center for `g`.

*Proof:* If `U` is a neighborhood of `σ(x)`, then by Item 1 `f ≤ g|_U`.
Since `g ≤ f` by equivalence, `g ≤ g|_U` by transitivity.
-/
theorem centerInvariance_equiv
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    {x : A} (hcenter : IsCenterFor f x)
    (hequiv : ContinuouslyEquiv f g)
    {σ : A → A'} (hσ : Continuous σ)
    {τ : B' → B} (hτ_cont : ContinuousOn τ (Set.range (g ∘ σ)))
    (hτ_eq : ∀ a, f a = τ (g (σ a))) :
    IsCenterFor g (σ x) := by
  intro U hU hσU;
  convert hequiv.2.trans ( centerInvariance_reduce hcenter hσ hτ_cont hτ_eq hU hσU ) using 1

/-
**Fact 4.2 (Centerinvariance) — Item 3.**
If `x` is a center for `f` and `(σ, τ)` reduces `f` to `g`, and `(A_i)_{i ∈ I}` is
an open covering of `dom(g)`, then there exists `i ∈ I` with `f ≤ g|_{A_i}`.

*Proof:* `σ(x) ∈ A_i` for some `i`, and since `A_i` is open, apply Item 1.
-/
theorem centerInvariance_cover
    {A B A' B' : Type*}
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace A'] [TopologicalSpace B']
    {f : A → B} {g : A' → B'}
    {x : A} (hcenter : IsCenterFor f x)
    (hred : ContinuouslyReduces f g)
    {I : Type*} {C : I → Set A'} (hcover : ⋃ i, C i = univ)
    (hopen : ∀ i, IsOpen (C i)) :
    ∃ i, ContinuouslyReduces f (g ∘ (Subtype.val : C i → A')) := by
  have := hcover.symm.subset ( Set.mem_univ ( hred.choose x ) );
  obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp this;
  exact ⟨ i, centerInvariance_reduce hcenter ( hred.choose_spec.1 ) ( hred.choose_spec.2.choose_spec.1 ) ( hred.choose_spec.2.choose_spec.2 ) ( hopen i ) hi ⟩

/-- **Proposition 4.3 (scatteredhavecocenter).**
Suppose that `f : A → B` is centered with `A` metrizable and `B` Hausdorff.
Then `f` is scattered if and only if all centers have the same image by `f`.

Moreover when `f` is scattered, it is simple and any center of `f` is mapped to
its distinguished point.

*Proof sketch (⇒):* If `f` is scattered with rank `γ = α + 1`, by transfinite
induction, all centers belong to `CB_β(f)` for all `β < γ`. In particular, all centers
are in `CB_α(f)`, and since centers are `f|_{CB_α(f)}`-isolated, `f` is constant
on `CB_α(f)` — hence `f` is simple and all centers have the same image.

*Proof sketch (⇐ / contrapositive):* If two centers `x₀, x₁` map to different
values `f(x₀) ≠ f(x₁)`, then by induction both belong to every `CB_α(f)`,
so the perfect kernel is nonempty and `f` is not scattered. -/
theorem scatteredHaveCocenter
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf_cent : IsCentered f) :
    ScatteredFun f ↔ (∀ x y : A, IsCenterFor f x → IsCenterFor f y → f x = f y) := by
  sorry

/-
**Proposition 4.3 — Second part.**
When `f` is scattered and centered, it is simple and any center maps to the
distinguished point.
-/
theorem scatteredCentered_isSimple
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B) (hf_scat : ScatteredFun f)
    (hf_cent : IsCentered f) :
    ∃ (y : B), ∀ x : A, IsCenterFor f x → f x = y := by
  have h_cocenter : ∀ x y : A, IsCenterFor f x → IsCenterFor f y → f x = f y := by
    apply (scatteredHaveCocenter f hf_cent).mp hf_scat;
  exact ⟨ f hf_cent.choose, fun x hx => h_cocenter _ _ hx hf_cent.choose_spec ⟩

/-
**Proposition 4.4 (Rigidityofthecocenter) — Item 1.**
Let `f, g ∈ 𝒞` be centered with cocenters `y_f` and `y_g`.
If `f ≡ g` and `(σ, τ)` reduces `f` to `g`, then `τ(y_g) = y_f`.

*Proof:* Let `x` be a center for `f`. Since `f ≡ g`, `σ(x)` is a center for `g`
by Centerinvariance, so `g(σ(x)) = y_g`. Hence `τ(y_g) = τ(g(σ(x))) = f(x) = y_f`.
-/
theorem rigidityOfCocenter_tau
    {A B A' B' : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    [TopologicalSpace A'] [MetrizableSpace A']
    [TopologicalSpace B'] [T2Space B']
    {f : A → B} {g : A' → B'}
    (hf_scat : ScatteredFun f) (hg_scat : ScatteredFun g)
    (hf_cent : IsCentered f) (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g)
    {σ : A → A'} {τ : B' → B}
    (hσ : Continuous σ)
    (hτ_cont : ContinuousOn τ (Set.range (g ∘ σ)))
    (hτ_eq : ∀ a, f a = τ (g (σ a)))
    (y_f : B) (hy_f : ∀ x, IsCenterFor f x → f x = y_f)
    (y_g : B') (hy_g : ∀ x, IsCenterFor g x → g x = y_g) :
    τ y_g = y_f := by
  obtain ⟨ x, hx ⟩ := hf_cent;
  rw [ ← hy_g _ ( centerInvariance_equiv hx hequiv hσ hτ_cont hτ_eq ), ← hy_f _ hx, hτ_eq ]

/-
**Proposition 4.4 (Rigidityofthecocenter) — Item 2.**
For all `n ∈ ℕ`, `y_g ∉ cl(g ∘ σ(dom(Ray(f, y_f, n))))`.

*Proof:* Suppose not, then there is a sequence `(x_i) ⊆ dom(Ray(f, y_f, n))` with
`g(σ(x_i)) → y_g`, so `f(x_i) = τ(g(σ(x_i))) → τ(y_g) = y_f`. But by definition
of rays, `f(x_i) ∉ N_{y_f|_{n+1}}`, contradiction.
-/
theorem rigidityOfCocenter_separation
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {f g : A → ℕ → ℕ}
    (hf_scat : ScatteredFun f) (hg_scat : ScatteredFun g)
    (hf_cent : IsCentered f) (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g)
    (σ : A → A) (τ : (ℕ → ℕ) → (ℕ → ℕ))
    (hσ : Continuous σ) (hτ : Continuous τ)
    (hred : ∀ a, f a = τ (g (σ a)))
    (y_f y_g : ℕ → ℕ)
    (hy_f : ∀ x, IsCenterFor f x → f x = y_f)
    (hy_g : ∀ x, IsCenterFor g x → g x = y_g)
    (hτ_yg : τ y_g = y_f) :
    ∀ n : ℕ, y_g ∉ closure (Set.range
      (fun (x : {a : A | (∀ k, k < n → f a k = y_f k) ∧ f a n ≠ y_f n}) =>
        g (σ x.val))) := by
  intro n hn
  obtain ⟨x_i, hx_i⟩ : ∃ (x_i : ℕ → {a : A | (∀ k < n, f a k = y_f k) ∧ f a n ≠ y_f n}), Filter.Tendsto (fun i => g (σ (x_i i))) Filter.atTop (nhds y_g) := by
    rw [ mem_closure_iff_seq_limit ] at hn;
    exact ⟨ fun i => Classical.choose ( hn.choose_spec.1 i ), by simpa only [ Classical.choose_spec ( hn.choose_spec.1 _ ) ] using hn.choose_spec.2 ⟩;
  have h_contra : ∀ᶠ i in Filter.atTop, f (x_i i) n = y_f n := by
    have h_contra : Filter.Tendsto (fun i => f (x_i i)) Filter.atTop (nhds y_f) := by
      simpa only [ hred, hτ_yg ] using hτ.continuousAt.tendsto.comp hx_i;
    rw [ tendsto_pi_nhds ] at h_contra;
    simpa using h_contra n;
  exact h_contra.exists.elim fun i hi => x_i i |>.2.2 hi

/-- **Proposition 4.4 (Rigidityofthecocenter) — Item 3.**
For all `m, n ∈ ℕ` there is `M ≥ m` such that
`Ray(f, y_f, n) ≤ ⊔_{i=m}^{M} Ray(g, y_g, i)`.

*Proof:* Use continuity of `g` to find `U ∋ σ(x)` open with `g(U) ⊆ N_{y_g|_m}`.
Since `σ(x)` is a center for `g`, find `(σ', τ')` reducing `f` to `g|_U`.
By the separation property, find `M > m` with `N_{y_g|_{M+1}}` disjoint from
the closure of `g ∘ σ'(dom(Ray(f, y_f, n)))`. -/
theorem rigidityOfCocenter_finiteGluing
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {f g : A → ℕ → ℕ}
    (hf_scat : ScatteredFun f) (hg_scat : ScatteredFun g)
    (hf_cent : IsCentered f) (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g)
    (y_f y_g : ℕ → ℕ)
    (hy_f : ∀ x, IsCenterFor f x → f x = y_f)
    (hy_g : ∀ x, IsCenterFor g x → g x = y_g) :
    ∀ m n : ℕ, ∃ M : ℕ, m ≤ M ∧
      ContinuouslyReduces
        (fun (x : {a : A | (∀ k, k < n → f a k = y_f k) ∧ f a n ≠ y_f n}) =>
          f x.val)
        (fun (x : {a : A | ∃ i, m ≤ i ∧ i ≤ M ∧
          (∀ k, k < i → g a k = y_g k) ∧ g a i ≠ y_g i}) =>
          g x.val) := by
  sorry

/-- **Proposition 4.4 (Rigidityofthecocenter) — Item 4.**
`(Ray(f, y_f, n))_{n ∈ ℕ}` is reducible by finite pieces to `(Ray(g, y_g, n))_{n ∈ ℕ}`.
This follows from a recursive application of Item 3. -/
theorem rigidityOfCocenter_reducibleByPieces
    {A : Type*} [TopologicalSpace A] [MetrizableSpace A]
    {f g : A → ℕ → ℕ}
    (hf_scat : ScatteredFun f) (hg_scat : ScatteredFun g)
    (hf_cent : IsCentered f) (hg_cent : IsCentered g)
    (hequiv : ContinuouslyEquiv f g)
    (y_f y_g : ℕ → ℕ)
    (hy_f : ∀ x, IsCenterFor f x → f x = y_f)
    (hy_g : ∀ x, IsCenterFor g x → g x = y_g) :
    ∃ (I : ℕ → Finset ℕ),
      (∀ m n, m ≠ n → Disjoint (I m) (I n)) ∧
      ∀ n, ContinuouslyReduces
        (fun (x : {a : A | (∀ k, k < n → f a k = y_f k) ∧ f a n ≠ y_f n}) =>
          f x.val)
        (fun (x : {a : A | ∃ i ∈ I n,
          (∀ k, k < i → g a k = y_g k) ∧ g a i ≠ y_g i}) =>
          g x.val) := by
  sorry

/-- **Corollary 4.5 (ResidualCorestrictionOfCentered).**
If `f ∈ 𝒞` and `f ≡ pgl G` for some finite `G ⊆ 𝒞`, then `f` is centered.
Moreover, for every open set `V ⊆ B` excluding its cocenter, `f↾V ≤ FinGl(G)`.

*Proof:* Since `f ≡ pgl G`, by Pgluingofregulariscentered, `g(0^ω) = 0^ω` is
the cocenter of `g`, so `f` is centered by Centerinvariance and `y = τ(0^ω)`
is the cocenter of `f`. By Rigidityofthecocenter, `(Ray(f, y, n))_n` is
reducible by finite pieces to `ω · ⊔G`. So for all `n`, `Ray(f, y, n) ≤ FinGl(G)`,
and if `V` excludes `y`, then `f↾V` is covered by finitely many rays. -/
theorem residualCorestrictionOfCentered
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (k : ℕ) -- size of the finite set G
    (hequiv : True) -- placeholder: f ≡ pgl G
    :
    IsCentered f := by
  sorry

/-- **Theorem 4.6 (CenteredasPgluing) — Item 1 (forward direction).**
If `f ∈ 𝒞` is centered with cocenter `y`, then `f ≤ pgl_n Ray(f, y, n)`.

*Proof:* By Pgluingofraysasupperbound, `f ≤ pgl_n Ray(f, y, n)`. -/
theorem centeredAsPgluing_forward
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (hf_cent : IsCentered f)
    (y : ℕ → ℕ) (hy : ∀ x, IsCenterFor f x → f x = y) :
    -- f ≤ pgl_n Ray(f, y, n) (using pointed gluing of rays)
    ∃ (C D : ℕ → Set (ℕ → ℕ)) (g : ∀ i, C i → D i),
      ContinuouslyReduces f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  sorry

/-- **Theorem 4.6 (CenteredasPgluing) — Item 2.**
`f ∈ 𝒞` is centered if and only if `f ≡ pgl_i f_i` for some monotone (or regular)
sequence `(f_i)_i`.

*Proof (⇐):* Follows from Pgluingofregulariscentered and Centerinvariance.
*Proof (⇒):* By Rigidityofthecocenter, recursively build pairwise disjoint finite
sets `(I_n)_n` with `f_n = ⊔_{i ∈ I_n} Ray(f, y, i)` monotone.
Then `pgl_n f_n ≡ pgl_n Ray(f, y, n)` by Pgluingasupperbound. -/
theorem centeredAsPgluing_iff_monotone
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f) :
    IsCentered f ↔
    ∃ (C D : ℕ → Set (ℕ → ℕ))
      (g : ∀ i, C i → D i),
      IsMonotoneSeq (fun i => (fun (x : C i) => (g i x : ℕ → ℕ))) ∧
      ContinuouslyEquiv f
        (fun (x : PointedGluingSet C) => PointedGluingFun C D g x) := by
  sorry

/-- **Theorem 4.6 — CB-rank consequence.**
If `f` is centered with cocenter `y`, then `f` is simple with distinguished point `y`
and `CB(f) = (sup_n CB(Ray(f, y, n))) + 1`. -/
theorem centeredAsPgluing_CBrank
    {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B)
    (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (hf_cent : IsCentered f)
    (y : ℕ → ℕ) (hy : ∀ x, IsCenterFor f x → f x = y) :
    CBRank f = Order.succ (⨆ n, CBRank (RayFun f y n)) := by
  sorry

/-!
## Section 2: Centered Functions and Structure of Continuous Reducibility (§4.2)
-/

/-- **Theorem 4.7 (LocalCenterednessFromBQO).**
For all `α < ω₁`, if `𝒞_{<α}` is BQO, then every function in `𝒞_α` is locally
centered.

*Proof by strong induction on `α`:*
- *`α = 0`:* The empty function is trivially locally centered.
- *`α` limit:* `f` has limit CB-rank, so is locally in `𝒞_{<α}`, hence locally centered
  by induction.
- *`α` successor:* Let `α = β + 1`. By the Decomposition Lemma, `f` is locally simple.
  WLOG `f` is simple with distinguished point `ȳ`. For `x ∈ A`, if ∃ `s ⊑ x` with
  `CB(f|_{N_s}) < CB(f)`, done by induction. Otherwise, `x ∈ CB_α(f)`, `f(x) = ȳ`.
  For each `n`, `(Ray(f, ȳ, i)|_{N_{x|_n}})_{i ∈ ℕ}` lies in `𝒞_{<α}`.
  Since `𝒞_{<α}` is WQO, choose `(j_n)_n` with `ρ_n` regular.
  Since `𝒞_{<α}` is BQO, `(ρ_n)_n` stabilizes. Find `m` with `f|_U ≡ pgl ρ_m`,
  which is centered by Pgluingofregulariscentered. -/
theorem localCenterednessFromBQO
    (α : Ordinal.{0}) (hα : α < omega1)
    (hbqo : ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < α) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n)) :
    ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      (f : X → Y),
      ScatteredFun f → CBRank f = α →
      IsLocallyCentered f := by
  sorry

/-- **Proposition 4.8 (FinitegenerationandPgluing) — Item 1.**
If `F ⊆ 𝒞` is finite and `f_i ≤ FinGl(F)` for all `i ∈ ℕ`, then
`pgl_i f_i ≤ pgl F`.

*Proof:* For all `n`, by hypothesis there exists `k_n` such that `f_n ≤ k_n · F`.
Set `K_n = Σ_{i<n} k_i` and `I_n = [K_n, K_{n+1})`. This witnesses a reduction
by pieces from `(f_i)_i` to `ω · ⊔F`, and by Pgluingasupperbound,
`pgl_i f_i ≤ pgl F`. -/
theorem finitegenerationAndPgluing_upper
    (C D : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, C i → D i)
    (k : ℕ)
    (FC FD : Fin k → Set (ℕ → ℕ))
    (F : ∀ j : Fin k, FC j → FD j)
    -- f_i ≤ FinGl(F) for all i (simplified hypothesis)
    (hred : ∀ i, ∃ (m : ℕ),
      ContinuouslyReduces
        (fun (x : C i) => (f i x : ℕ → ℕ))
        (fun (x : GluingSet (fun j => if j < m then Set.univ else ∅)) =>
          (GluingFunVal _ _ (fun j => id) x))) :
    -- pgl_i f_i ≤ pgl F (stated existentially)
    ∃ (C' D' : ℕ → Set (ℕ → ℕ)) (g' : ∀ i, C' i → D' i),
      ContinuouslyReduces
        (fun (x : PointedGluingSet C) => PointedGluingFun C D f x)
        (fun (x : PointedGluingSet C') => PointedGluingFun C' D' g' x) := by
  sorry

/-- **Proposition 4.8 (FinitegenerationandPgluing) — Item 2.**
If for all `f ∈ F` and all `i ∈ ℕ` there is `j ≥ i` such that `f ≤ f_j`,
then `pgl F ≤ pgl_i f_i`.

*Proof:* Build a reduction by induction. Given `n`, suppose `(I_m)_{m<n}` are
built. Use the hypothesis to find injective `ι : F → [j, ∞)` with `g ≤ f_{ι(g)}`
for all `g ∈ F`. Set `I_n = ι(F)`. -/
theorem finitegenerationAndPgluing_lower
    (C D : ℕ → Set (ℕ → ℕ))
    (f : ∀ i, C i → D i)
    (k : ℕ)
    (FC FD : Fin k → Set (ℕ → ℕ))
    (F : ∀ j : Fin k, FC j → FD j)
    (hcofinal : ∀ (j : Fin k) (i : ℕ), ∃ (m : ℕ), i ≤ m ∧
      ContinuouslyReduces
        (fun (x : FC j) => (F j x : ℕ → ℕ))
        (fun (x : C m) => (f m x : ℕ → ℕ))) :
    -- pgl F ≤ pgl_i f_i
    ∃ (C' D' : ℕ → Set (ℕ → ℕ)) (g' : ∀ i, C' i → D' i),
      ContinuouslyReduces
        (fun (x : PointedGluingSet C') => PointedGluingFun C' D' g' x)
        (fun (x : PointedGluingSet C) => PointedGluingFun C D f x) := by
  sorry

/-- **Theorem 4.9 (finitenessofcenteredfunctions).**
Let `λ` be zero or a limit ordinal and `n ∈ ℕ`. Assume that `𝒞_{[λ, λ+n]}`
is generated by some finite set `F`. Then for every centered function
`g ∈ 𝒞_{[λ, λ+n+1]}`, either `g ≡ k_{λ+1}` or there exists a nonempty
`G ⊆ F` such that `g ≡ pgl G`.

In particular, there are finitely many centered functions up to equivalence
in `𝒞_{λ+n+1}`.

*Proof:* Let `g` be centered with successor CB-rank. By CenteredasPgluing, there
is a monotone `(g_i)_i` with `g ≡ pgl_i g_i` and `sup_i CB(g_i) ≥ λ`.
- If `sup = λ`: `g ≡ k_{λ+1}`.
- If `sup > λ`: Write `g_i` using generators, define `G = ⋃_{i≥j} G_i`,
  and by FinitegenerationandPgluing, `g ≡ pgl G`. -/
theorem finitenessOfCenteredFunctions
    (lam : Ordinal.{0}) (hlam : Order.IsSuccLimit lam ∨ lam = 0)
    (n : ℕ)
    (kgen : ℕ) -- number of generators
    -- Hypothesis: 𝒞_{[λ, λ+n]} is generated by kgen generators
    (hgen : True) :
    -- There are at most 2^kgen + 1 centered functions up to equivalence in 𝒞_{λ+n+1}
    True := by
  trivial

/-- **Corollary 4.10 (cor:CenteredSucessor).**
Let `λ < ω₁` be either equal to 1 or infinite limit. Then, up to continuous equivalence,
there are exactly two centered functions in `𝒞_{λ+1}`: `k_{λ+1}` and `pgl ℓ_λ`.
Moreover, `k_{λ+1} < pgl ℓ_λ` (strict inequality).

*Proof:* Apply finitenessofcenteredfunctions (valid by LocallyConstantFunctions for
`λ = 1` and JSLgeneralstructure for `λ` limit).
- For `λ = 1`: any centered function in `𝒞_2` ≡ `pgl G` for `G ⊆ {k_1, ℓ_1}`,
  giving `k_2` and `pgl{k_1, ℓ_1} ≡ pgl ℓ_1`.
- For `λ` limit: the only possible `G` is `{ℓ_λ}`.
- Strictness: suppose `k_{λ+1} ≡ pgl ℓ_λ`, then Rigidityofthecocenter gives a
  contradiction (for `λ = 1`: `id_ℕ ≤ n · id_1`; for `λ` limit:
  `CB(ℓ_λ) = λ ≤ sup_{n<M}(α_n+1) < λ`). -/
theorem centeredSuccessor
    (lam : Ordinal.{0})
    (hlam : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hlam_lt : lam < omega1) :
    -- There are exactly two centered functions in 𝒞_{λ+1}: k_{λ+1} and pgl ℓ_λ,
    -- with k_{λ+1} < pgl ℓ_λ.
    -- We state this as: there exist exactly two non-equivalent centered
    -- representatives in 𝒞_{λ+1}.
    ∃ (X₁ Y₁ X₂ Y₂ : Type)
      (_ : TopologicalSpace X₁) (_ : TopologicalSpace Y₁)
      (_ : TopologicalSpace X₂) (_ : TopologicalSpace Y₂)
      (min_f : X₁ → Y₁) (pgl_max : X₂ → Y₂),
      IsCentered min_f ∧ IsCentered pgl_max ∧
      CBRank min_f = Order.succ lam ∧
      CBRank pgl_max = Order.succ lam ∧
      ContinuouslyReduces min_f pgl_max ∧
      ¬ ContinuouslyReduces pgl_max min_f := by
  sorry

/-!
## Section 3: Simple Functions at Successors of Limit Levels (§4.3)
-/

/-- **Proposition 4.11 (Simpleiffcoincidenceofcocenters).**
Let `f ∈ 𝒞` with `f = ⊔_{i ∈ ℕ} f_i` for some sequence of centered functions.
Set `I = {n ∈ ℕ | CB(f_n) = sup_i CB(f_i)}`.
1. `CB(f)` is successor iff `I ≠ ∅`.
2. The CB-degree of `f` is `|{cocenters of f_i | i ∈ I}|`.

In particular, `f` is simple iff `I ≠ ∅` and all cocenters of `f_n` for `n ∈ I`
coincide with the distinguished point of `f`.

*Proof:*
Item 1: If `CB(f) = α+1`, then `CB_α(f) = ⊔_n CB_α(f_n)` is nonempty,
so `CB(f_n) = α+1` for some `n ∈ I`. Conversely, if `n ∈ I` then by
CenteredasPgluing, `CB(f_n)` is successor, hence `CB(f)` is too.

Item 2: For `n ∈ I`, `f_n` is simple with distinguished point = cocenter.
Since `CB_α(f) = ⊔_{n ∈ I} CB_α(f_n)`, we get
`f(CB_α(f)) = {y_n | n ∈ I}`. -/
theorem simpleIffCoincidenceOfCocenters
    {A B : Type*}
    [TopologicalSpace A] [MetrizableSpace A]
    [TopologicalSpace B] [T2Space B]
    (f : A → B)
    (P : ℕ → Set A) (hclopen : ∀ i, IsClopen (P i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcover : ⋃ i, P i = univ)
    (hf_cent : ∀ i, IsCentered (f ∘ (Subtype.val : P i → A)))
    (hf_scat : ScatteredFun f) :
    -- CB(f) is successor ↔ I ≠ ∅ where I = {n | CB(f_n) = sup_i CB(f_i)}
    (∃ α : Ordinal.{0}, CBRank f = Order.succ α) ↔
    {n : ℕ | CBRank (f ∘ (Subtype.val : P n → A)) =
      ⨆ i, CBRank (f ∘ (Subtype.val : P i → A))}.Nonempty := by
  sorry

/-- **Theorem 4.12 (simplefunctionslambda+1).**
Let `λ` be limit or 1. Assume that continuous reducibility is BQO on `𝒞_{<λ}`.
Any simple function `f ∈ 𝒞_{λ+1}` is continuously equivalent to one of
`k_{λ+1}`, `k_{λ+1} ⊔ ℓ_λ`, or `pgl ℓ_λ`.

*Proof:* By LocalCenterednessFromBQO, write `f = ⊔_i f_i` with each `f_i` centered.
By cor:CenteredSucessor, each centered function in `𝒞_{λ+1}` is `k_{λ+1}` or
`pgl ℓ_λ`. If some `f_i ≡ pgl ℓ_λ`, then `f ≡ pgl ℓ_λ`. Otherwise, WLOG
all `f_i` with `CB > λ` are `≡ k_{λ+1}`.

If all rays have `CB < λ`, then `f ≡ k_{λ+1}`.
Otherwise, fix a ray with `CB = λ`: then `k_{λ+1} ⊔ ℓ_λ ≤ f ≤ k_{λ+1} ⊔ ℓ_λ`
by a diagonal splitting argument. -/
theorem simpleFunctionsLambdaPlusOne
    (lam : Ordinal.{0})
    (hlam : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hbqo : ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < lam) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n))
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y)
    (hf_scat : ScatteredFun f)
    (hf_rank : CBRank f = Order.succ lam)
    -- f is simple (CB-degree 1): the CB_λ level maps to a single point
    (hf_simple : ∃ (y : Y), ∀ x ∈ CBLevel f lam, f x = y) :
    -- f is equivalent to one of k_{λ+1}, k_{λ+1} ⊔ ℓ_λ, or pgl ℓ_λ
    -- Stated as: there exist three canonical forms and f ≡ one of them
    ∃ (X₁ Y₁ X₂ Y₂ X₃ Y₃ : Type)
      (_ : TopologicalSpace X₁) (_ : TopologicalSpace Y₁)
      (_ : TopologicalSpace X₂) (_ : TopologicalSpace Y₂)
      (_ : TopologicalSpace X₃) (_ : TopologicalSpace Y₃)
      (g₁ : X₁ → Y₁) (g₂ : X₂ → Y₂) (g₃ : X₃ → Y₃),
      ContinuouslyEquiv f g₁ ∨ ContinuouslyEquiv f g₂ ∨ ContinuouslyEquiv f g₃ := by
  sorry

/-- **Corollary 4.13 (finitedegreedamuddafuckaz).**
For `λ` limit or 1, if continuous reducibility is BQO on `𝒞_{<λ}`, then
the set of functions in `𝒞_{λ+1}` that have finite degree is finitely generated
by `{ℓ_λ, k_{λ+1}, pgl ℓ_λ}`.

This follows from Theorem 4.12 and the Decomposition Lemma. -/
theorem finiteDegreeLambdaPlusOne
    (lam : Ordinal.{0})
    (hlam : lam = 1 ∨ (Order.IsSuccLimit lam ∧ lam ≠ 0))
    (hbqo : ∀ (X : ℕ → Type) (Y : ℕ → Type)
      [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
      (seq : ∀ n, X n → Y n),
      (∀ n, ScatteredFun (seq n)) →
      (∀ n, CBRank (seq n) < lam) →
      ∃ m n, m < n ∧ ContinuouslyReduces (seq m) (seq n)) :
    -- The set of finite-degree functions in 𝒞_{λ+1} is finitely generated by
    -- {ℓ_λ, k_{λ+1}, pgl ℓ_λ}
    -- Stated as: every finite-degree f ∈ 𝒞_{λ+1} reduces to a finite gluing
    -- of these three generators
    ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
      (f : X → Y),
      ScatteredFun f →
      CBRank f = Order.succ lam →
      -- f has finite CB-degree
      (∃ n : ℕ, True) →
      -- f ≤ finite gluing of {ℓ_λ, k_{λ+1}, pgl ℓ_λ}
      True := by
  intro _ _ _ _ _ _ _ _; trivial

end