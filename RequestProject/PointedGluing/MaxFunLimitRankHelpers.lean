import Mathlib
import RequestProject.BaireSpace.Basics

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-! ## Helper lemmas for the antichain construction in MaxFunLimitRank -/

lemma nat_range_infinite_or_fiber_infinite (g : ℕ → ℕ) :
    (Set.range g).Infinite ∨ ∃ v, (g ⁻¹' {v}).Infinite := by
  by_contra!
  exact Set.infinite_univ (Set.Finite.subset (Set.Finite.biUnion this.1 fun x hx => this.2 x) fun x _ => by aesop)

lemma injective_subseq_of_infinite_range (g : ℕ → ℕ) (h : (Set.range g).Infinite) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ Injective (g ∘ a) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ n, g (a n) ∉ Finset.image g (Finset.range (a n)) := by
    have h_infinite_range : ∀ n, ∃ m ≥ n, g m ∉ Finset.image g (Finset.range m) := by
      intro n; by_contra h_contra; push_neg at h_contra
      have h_range_subset : Set.range g ⊆ Finset.image g (Finset.range n) := by
        rintro x ⟨m, rfl⟩; induction' m using Nat.strong_induction_on with m ih
        rcases lt_or_ge m n with hm | hm <;> simp_all +decide [Finset.mem_image]
        · exact ⟨m, hm, rfl⟩
        · obtain ⟨a, ha₁, ha₂⟩ := h_contra m hm; obtain ⟨x, hx₁, hx₂⟩ := ih a ha₁; exact ⟨x, hx₁, hx₂.trans ha₂⟩
      exact h (Set.Finite.subset (Finset.finite_toSet _) h_range_subset)
    exact ⟨fun n => Nat.recOn n (Nat.find (h_infinite_range 0)) fun n ih => Nat.find (h_infinite_range (ih + 1)),
      strictMono_nat_of_lt_succ fun n => Nat.find_spec (h_infinite_range _) |>.1.trans_lt' (Nat.lt_succ_self _),
      fun n => Nat.recOn n (Nat.find_spec (h_infinite_range 0) |>.2) fun n ih => Nat.find_spec (h_infinite_range _) |>.2⟩
  exact ⟨a, ha.1, fun x y hxy => le_antisymm
    (le_of_not_gt fun hxy' => ha.2 _ <| Finset.mem_image.mpr ⟨a y, Finset.mem_range.mpr <| ha.1 hxy', hxy.symm⟩)
    (le_of_not_gt fun hxy' => ha.2 _ <| Finset.mem_image.mpr ⟨a x, Finset.mem_range.mpr <| ha.1 hxy', hxy⟩)⟩

/-- Case 1: branching level antichain -/
lemma branching_level_antichain (f : ℕ → (ℕ → ℕ)) (k : ℕ)
    (_hprefix : ∀ i j : ℕ, ∀ m : ℕ, m < k → f i m = f j m)
    (hinj : Injective (fun i => f i k)) :
    ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
      (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧ ¬IsPrefix (seq j).2 (seq i).2) ∧
      ∀ i, ∀ j : Fin (seq i).1, (seq i).2 j = f i j := by
  refine' ⟨fun i ↦ ⟨k + 1, fun j ↦ f i j⟩, _, _⟩ <;> simp +decide [IsPrefix]
  exact fun i j hij => ⟨⟨⟨k, Nat.lt_succ_self _⟩, fun h => hij <| hinj <| by simpa using h⟩,
    ⟨⟨k, Nat.lt_succ_self _⟩, fun h => hij <| hinj <| by simpa using h.symm⟩⟩

/-- Case 2: orphan extraction antichain -/
lemma orphan_antichain
    (f : ℕ → (ℕ → ℕ)) (v : ℕ → ℕ)
    (levels : ℕ → ℕ) (hlev_strict : StrictMono levels)
    (hagree : ∀ n m, m < levels n → f n m = v m)
    (hdiffer : ∀ n, f n (levels n) ≠ v (levels n)) :
    ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
      (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧ ¬IsPrefix (seq j).2 (seq i).2) ∧
      ∀ i, ∀ j : Fin (seq i).1, (seq i).2 j = f i j := by
  refine' ⟨fun i => ⟨levels i + 1, fun j => f i j⟩, _, _⟩ <;> simp +decide [IsPrefix]
  intro i j hij; cases lt_or_gt_of_ne hij <;> simp_all +decide [hlev_strict.lt_iff_lt]
  · exact fun _ => ⟨⟨levels i, by linarith [hlev_strict ‹_›]⟩,
      by specialize hdiffer i; specialize hagree j (levels i) (by linarith [hlev_strict ‹_›]); aesop⟩
  · exact fun _ => ⟨⟨levels j, Nat.lt_succ_self _⟩,
      by specialize hdiffer j; specialize hagree i (levels j) (hlev_strict ‹_›); aesop⟩

/-- Key combinatorial lemma: given an injective function from ℕ to Baire space,
    we can find infinitely many finite truncations forming an antichain. -/
lemma infinite_baire_antichain_prefixes (f : ℕ → (ℕ → ℕ)) (hf : Injective f) :
    ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
      (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧ ¬IsPrefix (seq j).2 (seq i).2) ∧
      ∀ i, ∃ m, ∀ j : Fin (seq i).1, (seq i).2 j = f m j := by
  sorry

end
