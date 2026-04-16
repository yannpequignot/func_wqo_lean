import Mathlib
import RequestProject.IntroMemo

open scoped Topology
open Set Function TopologicalSpace

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `2_prelim_memo.tex` — Basic Results

This file formalizes the basic results from the preliminaries chapter of the memoir
on continuous reducibility between functions.

## Main definitions

* `WadgeReduces` — Wadge reducibility between subsets
* `TopologicallyEmbedsFun` — topological embeddability between functions
* `corestriction'` — co-restriction of a function to a subset of the codomain

## Main results

* `embedding_iff_id_reduces` — X embeds in Y iff id_X ≤ id_Y
* `restriction_reduces` — f|_A ≤ f for A ⊆ dom f
* `ContinuouslyReduces.sigma_injective` — if f is injective and (σ,τ) reduces f to g,
  then σ is injective
-/

section CoRestriction

/-- The co-restriction of `f : X → Y` to `B ⊆ Y` is the restriction of `f` to `f⁻¹(B)`.
That is, `f` viewed as a function from `f⁻¹(B)` to `Y`. -/
def corestriction' {X Y : Type*} (f : X → Y) (B : Set Y) :
    f ⁻¹' B → Y :=
  f ∘ Subtype.val

end CoRestriction

section WadgeReducibility

/-- `WadgeReduces A B` means that the set `A` Wadge reduces to the set `B`:
there exists a continuous function `σ` such that `σ⁻¹(B) = A`. -/
def WadgeReduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) : Prop :=
  ∃ (σ : X → Y), Continuous σ ∧ σ ⁻¹' B = A

end WadgeReducibility

section TopologicalEmbeddabilityFunctions

/-- `TopologicallyEmbedsFun f g` means that `f` topologically embeds in `g`:
there exist `σ` and `τ` that are both topological embeddings and
satisfy `f = τ ∘ g ∘ σ`. -/
def TopologicallyEmbedsFun {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ (σ : X → X') (τ : Y' → Y),
    Topology.IsEmbedding σ ∧ Topology.IsEmbedding τ ∧ ∀ x, f x = τ (g (σ x))

/-- Topological embeddability implies continuous reducibility. -/
theorem TopologicallyEmbedsFun.continuouslyReduces {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (h : TopologicallyEmbedsFun f g) : ContinuouslyReduces f g := by
  obtain ⟨σ, τ, hσ, hτ, hred⟩ := h
  exact ⟨σ, τ, hσ.continuous, hτ.continuous, hred⟩

end TopologicalEmbeddabilityFunctions

section EmbeddingAndReduction

/-- If `id_X` continuously reduces to `id_Y`, then `X` topologically embeds in `Y`.

**Note:** The converse (embedding implies reduction) holds in the paper's definition
where `τ` is only required on `im(g ∘ σ)`, but fails with our total-`τ` definition.
For example, `ℕ` embeds in `ℝ` but there is no continuous `τ : ℝ → ℕ` since `ℝ` is
connected and `ℕ` is discrete. -/
theorem embedding_of_id_reduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuouslyReduces (@id X) (@id Y)) :
    ∃ (σ : X → Y), Topology.IsEmbedding σ := by
  obtain ⟨σ, τ, hσ, hτ, hred⟩ := h
  have hid : ∀ x, τ (σ x) = x := fun x => (hred x).symm
  exact ⟨σ, ⟨⟨by ext s; exact ⟨fun hs => ⟨τ ⁻¹' s, hτ.isOpen_preimage s hs,
    by ext x; simp [hid]⟩, fun ⟨t, ht, e⟩ => e ▸ hσ.isOpen_preimage t ht⟩⟩,
    LeftInverse.injective hid⟩⟩

end EmbeddingAndReduction

section BasicReductionFacts

/-- Restriction to a subset reduces to the whole function. -/
theorem restriction_reduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) :
    ContinuouslyReduces (f ∘ (Subtype.val : A → X)) f :=
  ⟨Subtype.val, id, continuous_subtype_val, continuous_id, fun _ => rfl⟩

/-- If `f : X → Y` is continuous and `X` is a retract of `Z` (i.e., there exist
continuous `σ : X → Z` and `τ : Z → X` with `τ ∘ σ = id`), then `f ≤ id_Z`.

**Note:** The paper requires only that `dom f` embeds in `X`, but our total-`τ` formalization
of `ContinuouslyReduces` requires a global retraction. -/
theorem reduces_to_id_of_retract {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f)
    {σ : X → Z} (hσ : Continuous σ)
    {τ : Z → X} (hτ : Continuous τ)
    (hστ : ∀ x, τ (σ x) = x) :
    ContinuouslyReduces f (@id Z) :=
  ⟨σ, f ∘ τ, hσ, hf.comp hτ, fun x => by simp [hστ]⟩

end BasicReductionFacts

section ContRedonEmbed

/-- If `(σ,τ)` reduces an injective `f` to `g`, then `σ` is injective. -/
theorem ContinuouslyReduces.sigma_injective
    {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hf : Injective f)
    (hred : ∀ x, f x = τ (g (σ x))) : Injective σ := by
  intro x1 x2 hσ
  have : f x1 = f x2 := by rw [hred x1, hred x2, hσ]
  exact hf this

/-- If `(σ,τ)` reduces an injective `f` to `g`, then `τ` is injective on the range
of `g ∘ σ`. -/
theorem ContinuouslyReduces.tau_injective_on_range
    {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    {σ : X → X'} {τ : Y' → Y}
    (hf : Injective f)
    (hred : ∀ x, f x = τ (g (σ x))) : InjOn τ (Set.range (g ∘ σ)) := by
  intro y1 hy1 y2 hy2 hτ
  obtain ⟨x1, rfl⟩ := hy1
  obtain ⟨x2, rfl⟩ := hy2
  simp [comp_apply] at hτ
  have h1 : f x1 = f x2 := by rw [hred x1, hred x2, hτ]
  rw [hf h1]

end ContRedonEmbed

section HomeomorphicFunctions

/-- Two functions are homeomorphic if there are homeomorphisms `σ` and `τ` such that
`f = τ ∘ f' ∘ σ`. -/
def HomeomorphicFun {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (f' : X' → Y') : Prop :=
  ∃ (σ : X ≃ₜ X') (τ : Y' ≃ₜ Y), ∀ x, f x = τ (f' (σ x))

/-- Homeomorphic functions are continuously equivalent. -/
theorem HomeomorphicFun.continuouslyEquiv {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {f' : X' → Y'}
    (h : HomeomorphicFun f f') : ContinuouslyEquiv f f' := by
  obtain ⟨σ, τ, hred⟩ := h
  constructor
  · exact ⟨σ, τ, σ.continuous, τ.continuous, hred⟩
  · refine ⟨σ.symm, τ.symm, σ.symm.continuous, τ.symm.continuous, fun x' => ?_⟩
    have := hred (σ.symm x')
    simp at this
    rw [this]; simp

end HomeomorphicFunctions
