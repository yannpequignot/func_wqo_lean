import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs
import RequestProject.PointedGluing.CBRankHelpers
import RequestProject.PointedGluing.CBLevelOpenRestrict
import RequestProject.PointedGluing.CBRankSimpleHelpers
import RequestProject.PointedGluing.UpperBoundHelpers
import RequestProject.PointedGluing.MaxMinhelpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
## Self-similarity of MaxFun: GluingSet(fun _ => MaxDom α) ≤ MaxFun α

This file proves that countably many copies of MaxFun α reduce to MaxFun α.
This is the key "self-similarity" property needed for combining local reductions.
-/

/-
Helper: flatten GluingSet of GluingSet with constant blocks.
Maps [i, j, y₀, ...] → [pair(i,j), y₀, ...]
Recovery: [k, y₀, ...] → [fst k, snd k, y₀, ...]
-/
lemma gluingSet_flatten_const (S : Set (ℕ → ℕ)) :
    ContinuouslyReduces
      (fun x : GluingSet (fun _ => GluingSet (fun _ => S)) => x.val)
      (fun x : GluingSet (fun _ => S) => x.val) := by
  constructor;
  swap;
  exact fun x => ⟨ prepend ( Nat.pair ( x.val 0 ) ( x.val 1 ) ) ( fun k => x.val ( k + 2 ) ), by
    obtain ⟨ i, hi ⟩ := Set.mem_iUnion.mp x.2;
    obtain ⟨ y, hy, hy' ⟩ := hi;
    obtain ⟨ j, hj ⟩ := Set.mem_iUnion.mp hy;
    obtain ⟨ z, hz, rfl ⟩ := hj;
    simp +decide [ ← hy', prepend ];
    exact Set.mem_iUnion.mpr ⟨ Nat.pair i j, Set.mem_image_of_mem _ hz ⟩ ⟩;
  all_goals generalize_proofs at *;
  refine' ⟨ _, _ ⟩;
  · refine' Continuous.subtype_mk _ _;
    refine' continuous_pi fun k => _;
    induction' k with k ih;
    · exact Continuous.comp ( show Continuous fun x : ℕ × ℕ => Nat.pair x.1 x.2 from by continuity ) ( Continuous.prodMk ( continuous_apply 0 |> Continuous.comp <| continuous_subtype_val ) ( continuous_apply 1 |> Continuous.comp <| continuous_subtype_val ) );
    · exact continuous_apply ( k + 2 ) |> Continuous.comp <| continuous_subtype_val;
  · refine' ⟨ _, _, _ ⟩;
    exact fun x => fun k => if k = 0 then Nat.unpair ( x 0 ) |>.1 else if k = 1 then Nat.unpair ( x 0 ) |>.2 else x ( k - 1 );
    · refine' Continuous.continuousOn _;
      fun_prop;
    · intro x; ext k; rcases k with ( _ | _ | k ) <;> simp +decide [ prepend ] ;

/-
Self-similarity: GluingSet(fun _ => MaxDom α) ≤ MaxFun α.
Proved by transfinite induction on α.
- Base (α = 0): both domains are empty.
- Successor (α = β+1): use gluingSet_flatten_const since MaxDom(β+1) = GluingSet(fun _ => SuccMaxDom β).
- Limit: use IH at each enumBelow α j to absorb the outer index into the inner content.
-/
lemma gluingSet_copies_reduces_to_MaxFun (α : Ordinal.{0}) (hα : α < omega1) :
    ContinuouslyReduces
      (fun x : GluingSet (fun _ => MaxDom α) => (x.val : ℕ → ℕ))
      (MaxFun α) := by
  sorry

/-
Combining local reductions: if f is covered by a Baire-clopen partition
and each piece reduces to MaxFun α, then f ≤ MaxFun α.
Uses gluingSet_copies_reduces_to_MaxFun for the final step.
-/
lemma combine_local_reductions
    {A : Set (ℕ → ℕ)} {α : Ordinal.{0}} (hα : α < omega1)
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (W : ℕ → Set (ℕ → ℕ))
    (hW_clopen : ∀ m, IsClopen (W m))
    (hW_disj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hW_cover : ∀ x : A, ∃ m, x.val ∈ W m)
    (hred : ∀ m, ContinuouslyReduces
      (fun x : {a : A | a.val ∈ W m} => f x.val)
      (MaxFun α)) :
    ContinuouslyReduces f (MaxFun α) := by
  sorry

/-
Main lemma: the CBRank f = α case of maxFun_item1_from_ih'.
-/
lemma cbrank_eq_case
    (α : Ordinal.{0}) (hα : α < omega1)
    (ih1 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (_hf : Continuous f) (_hscat : ScatteredFun f)
      (_hcb : ∀ γ : Ordinal.{0}, β ≤ γ → CBLevel f γ = ∅),
      ContinuouslyReduces f (MaxFun β))
    (ih2 : ∀ (β : Ordinal.{0}), β < α → ∀ {A : Set (ℕ → ℕ)}
      (f : A → ℕ → ℕ) (hf : Continuous f)
      (γ : Ordinal.{0}) (hγ : γ ≤ β)
      (hcb_ne : (CBLevel f γ).Nonempty)
      (hcb_empty : CBLevel f (Order.succ γ) = ∅)
      (y : ℕ → ℕ)
      (hy_simple : ∀ x ∈ CBLevel f γ, f x = y),
      ContinuouslyReduces f (SuccMaxFun β))
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (hscat : ScatteredFun f)
    (hcb : ∀ β : Ordinal.{0}, α ≤ β → CBLevel f β = ∅)
    (h_empty : (CBLevel f 0).Nonempty)
    (hrank_eq : CBRank f = α) :
    ContinuouslyReduces f (MaxFun α) := by
  sorry

end