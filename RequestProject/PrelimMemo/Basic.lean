import RequestProject.IntroMemo
import RequestProject.BaireSpace.Basics
open scoped Topology
open Set Function TopologicalSpace

set_option autoImplicit false

/-!
# Formalization of `2_prelim_memo.tex` — Basic Results

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

/-- The co-restriction of `f : X → Y` to `B ⊆ Y` is the restriction of `f` to `f⁻¹(B)`. -/
def corestriction' {X Y : Type*} (f : X → Y) (B : Set Y) : f ⁻¹' B → Y :=
  f ∘ Subtype.val

end CoRestriction

section WadgeReducibility

/-- `WadgeReduces A B` means that the set `A` Wadge reduces to the set `B`. -/
def WadgeReduces {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) : Prop :=
  ∃ (σ : X → Y), Continuous σ ∧ σ ⁻¹' B = A

end WadgeReducibility

section TopologicalEmbeddabilityFunctions

/-- `TopologicallyEmbedsFun f g` means that `f` topologically embeds in `g`. -/
def TopologicallyEmbedsFun {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (f : X → Y) (g : X' → Y') : Prop :=
  ∃ (σ : X → X') (τ : Y' → Y),
    Topology.IsEmbedding σ ∧ Topology.IsEmbedding τ ∧ ∀ x, f x = τ (g (σ x))

theorem TopologicallyEmbedsFun.continuouslyReduces {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {g : X' → Y'}
    (h : TopologicallyEmbedsFun f g) : ContinuouslyReduces f g := by
  obtain ⟨σ, τ, hσ, hτ, hred⟩ := h
  exact ⟨σ, hσ.continuous, τ, hτ.continuous.continuousOn, hred⟩

end TopologicalEmbeddabilityFunctions

section EmbeddingAndReduction

theorem embedding_of_id_reduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (h : ContinuouslyReduces (@id X) (@id Y)) :
    ∃ (σ : X → Y), Topology.IsEmbedding σ := by
  obtain ⟨σ, τ, hσ, hτ, h⟩ := h
  have h_inj : Function.Injective (fun x : X => ⟨σ x, Set.mem_range_self x⟩ : X → Set.range σ) := by
    intro x y hxy; grind
  have h_embedding : Topology.IsEmbedding (fun x : X => ⟨σ x, Set.mem_range_self x⟩ : X → Set.range σ) := by
    refine ⟨?_, h_inj⟩
    rw [Topology.isInducing_iff_nhds]; intro x
    refine le_antisymm ?_ ?_
    · rw [Filter.le_def]
      simp +decide [Filter.mem_comap, nhds_induced]
      intro U V W hW hV hU
      filter_upwards [τ.continuousAt hW] with y hy using hU <| hV <| by simpa using hy
    · intro s hs
      refine ⟨{y : {x // x ∈ range σ} | hσ y.val ∈ s}, ?_, ?_⟩
      · rw [mem_nhds_iff] at hs ⊢
        obtain ⟨t, ht₁, ht₂, ht₃⟩ := hs
        refine ⟨{y : {x // x ∈ range σ} | hσ y.val ∈ t}, fun y hy => ht₁ hy,
          ht₂.preimage (hτ.comp_continuous continuous_subtype_val fun x => by simp +decide),
          by grind +splitImp⟩
      · grind
  refine ⟨?_, ?_⟩
  exact fun x => σ x
  rw [Topology.isEmbedding_iff] at *
  rw [Topology.isInducing_iff_nhds] at *
  convert h_embedding using 1
  · simp +decide [nhds_induced, Filter.comap_comap]
    rfl
  · simp +decide [Function.Injective]

end EmbeddingAndReduction

section BasicReductionFacts

theorem restriction_reduces {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (A : Set X) :
    ContinuouslyReduces (f ∘ (Subtype.val : A → X)) f :=
  ⟨Subtype.val, continuous_subtype_val, id, continuousOn_id, fun _ => rfl⟩

theorem reduces_to_id_of_retract {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} (hf : Continuous f)
    {σ : X → Z} (hσ : Continuous σ)
    {τ : Z → X} (hτ : Continuous τ)
    (hστ : ∀ x, τ (σ x) = x) :
    ContinuouslyReduces f (@id Z) :=
  ⟨σ, hσ, f ∘ τ, (hf.comp hτ).continuousOn, fun x => by simp [hστ x]⟩

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
    (hred : ∀ x, f x = τ (g (σ x))) : Injective σ :=
  fun x1 x2 hσ => hf (by rw [hred x1, hred x2, hσ])

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
  rintro _ ⟨x1, rfl⟩ _ ⟨x2, rfl⟩ hτ
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

theorem HomeomorphicFun.continuouslyEquiv {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    {f : X → Y} {f' : X' → Y'}
    (h : HomeomorphicFun f f') : ContinuouslyEquiv f f' := by
  obtain ⟨σ, τ, hred⟩ := h
  constructor
  · exact ⟨σ, σ.continuous, τ, τ.continuous.continuousOn, hred⟩
  · refine ⟨σ.symm, σ.symm.continuous, τ.symm, τ.symm.continuous.continuousOn, fun x' => ?_⟩
    have := hred (σ.symm x'); simp at this; rw [this]; simp

end HomeomorphicFunctions

section Notations

/-- `ω₁` as a countable ordinal. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord

end Notations
