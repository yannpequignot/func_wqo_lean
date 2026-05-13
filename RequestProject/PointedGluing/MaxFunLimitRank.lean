import RequestProject.PointedGluing.GeneralStructureHelpers
import Mathlib

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

def gClopenDom (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∃ (h : x ∈ B), g ⟨x, h⟩ ∈ C}

def gClopenFun (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    gClopenDom B g C → ℕ → ℕ :=
  fun ⟨x, hx⟩ => g ⟨x, hx.choose⟩

lemma gClopenFun_continuous (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (C : Set (ℕ → ℕ)) :
    Continuous (gClopenFun B g C) :=
  hgc.comp (Continuous.subtype_mk continuous_subtype_val _)

lemma gClopenFun_scattered (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hg : ScatteredFun g) (C : Set (ℕ → ℕ)) :
    ScatteredFun (gClopenFun B g C) := by
  have : ContinuouslyReduces (gClopenFun B g C) g :=
    ⟨fun x => ⟨x.val, x.prop.choose⟩,
     Continuous.subtype_mk continuous_subtype_val _,
     id, continuousOn_id, fun x => rfl⟩
  exact this.scattered hg

lemma exists_disjoint_clopen_with_cofinal_ranks
    (η : Ordinal.{0}) (hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g) (hg : ScatteredFun g)
    (hrank : CBRank g = η)
    (δ : ℕ → Ordinal.{0}) (hδ : ∀ n, δ n < η) :
    ∃ (C : ℕ → Set (ℕ → ℕ)) (p : ℕ → ℕ),
      Function.Injective p ∧
      (∀ n, IsClopen (C n)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ n, δ n < CBRank (gClopenFun B g (C (p n))) := by
  sorry

private lemma extract_B_map
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ))
    {A : Set (ℕ → ℕ)}
    (hred : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (gClopenFun B g C)) :
    ∃ (σ : A → B) (τ : (ℕ → ℕ) → (ℕ → ℕ)),
      Continuous σ ∧
      ContinuousOn τ (Set.range (g ∘ σ)) ∧
      (∀ x, g (σ x) ∈ C) ∧
      (∀ x : A, x.val = τ (g (σ x))) := by
  obtain ⟨σ₀, hσ₀_cont, τ₀, hτ₀_cont, hτ₀_eq⟩ := hred
  refine ⟨fun x => ⟨(σ₀ x).val, (σ₀ x).prop.choose⟩, τ₀, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp hσ₀_cont) _
  · convert hτ₀_cont using 1
  · exact fun x => (σ₀ x).prop.choose_spec
  · exact hτ₀_eq

lemma gluing_via_codomain_partition
    (η : Ordinal.{0}) (hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g)
    (C : ℕ → Set (ℕ → ℕ))
    (hC_clopen : ∀ n, IsClopen (C n))
    (hC_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (p : ℕ → ℕ) (hp : Function.Injective p)
    (hred : ∀ n, ContinuouslyReduces
        (Subtype.val : MaxDom (enumBelow η n) → ℕ → ℕ)
        (gClopenFun B g (C (p n)))) :
    ContinuouslyReduces (MaxFun η) g := by
  sorry

end
