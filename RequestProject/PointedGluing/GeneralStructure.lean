import RequestProject.PointedGluing.GeneralStructureHelpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
# General Structure Theorem (Theorem 3.13)

This file proves the General Structure Theorem for continuous reducibility
between scattered functions on the Baire space.
-/

private lemma omega1_add_nat (η : Ordinal.{0}) (hη : η < omega1) (n : ℕ) :
    η + ↑n < omega1 := by
  induction n with
  | zero => simpa
  | succ n ih =>
    calc η + (↑(n + 1) : Ordinal) = Order.succ (η + ↑n) := by
          rw [Nat.cast_succ, ← Ordinal.add_one_eq_succ, add_assoc]
    _ < omega1 :=
          (Cardinal.isSuccLimit_ord (Cardinal.aleph0_le_aleph 1)).succ_lt ih

private lemma cblevel_empty_of_le
    {A : Set (ℕ → ℕ)} (f : A → ℕ → ℕ) (hf_scat : ScatteredFun f)
    (β : Ordinal.{0}) (hle : CBRank f ≤ β) :
    CBLevel f β = ∅ :=
  Set.eq_empty_of_subset_empty
    ((CBLevel_eq_empty_at_rank f hf_scat) ▸ CBLevel_antitone f hle)

/-- Base case: MaxFun(η) ≤ MinFun(η) for η = 0. -/
private lemma MaxFun_le_MinFun_zero :
    ContinuouslyReduces (MaxFun 0) (MinFun 0) := by
  haveI : IsEmpty (MaxDom 0) := by rw [MaxDom_zero]; exact Set.isEmpty_coe_sort.mpr rfl
  exact continuouslyReduces_of_empty (MaxFun 0) (MinFun 0)

/-- For any sequence of ordinals below a limit, there's an injective
    map into ℕ picking indices of cofinalSeq above each target. -/
private lemma exists_injection_above_targets (η : Ordinal.{0}) (hη : η < omega1)
    (hlim : Order.IsSuccLimit η)
    (β : ℕ → Ordinal.{0}) (hβ : ∀ n, β n < η) :
    ∃ p : ℕ → ℕ, Function.Injective p ∧ ∀ n, β n ≤ cofinalSeq η (p n) := by
  sorry

/-- Base case: MaxFun(η) ≤ MinFun(η) for limit η. -/
private lemma MaxFun_le_MinFun_limit (η : Ordinal.{0}) (hη : η < omega1)
    (hlim : Order.IsSuccLimit η) :
    ContinuouslyReduces (MaxFun η) (MinFun η) := by
  sorry

/-- Core inequality: MaxFun(η + n) ≤ MinFun(η + 2n).
    Proved by induction on n, with the successor step using MaxFun_le_MinFun_succ. -/
private lemma MaxFun_le_MinFun (η : Ordinal.{0}) (hη : η < omega1)
    (hlam : Order.IsSuccLimit η ∨ η = 0) (n : ℕ) :
    ContinuouslyReduces (MaxFun (η + ↑n)) (MinFun (η + 2 * ↑n)) := by
  induction n with
  | zero =>
    have : η + ↑(0 : ℕ) = η := by norm_num
    have : η + 2 * ↑(0 : ℕ) = η := by norm_num
    rw [‹η + ↑(0 : ℕ) = η›, ‹η + 2 * ↑(0 : ℕ) = η›]
    rcases hlam with hlim | h0
    · exact MaxFun_le_MinFun_limit η hη hlim
    · subst h0; exact MaxFun_le_MinFun_zero
  | succ n ih =>
    -- η + (n+1) = Order.succ (η + n) and η + 2*(n+1) = Order.succ (Order.succ (η + 2n))
    have h1 : η + ↑(n + 1) = Order.succ (η + ↑n) := by
      rw [Nat.cast_succ, ← Ordinal.add_one_eq_succ, add_assoc]
    have h2 : η + 2 * ↑(n + 1) = Order.succ (Order.succ (η + 2 * ↑n)) := by
      simp only [Nat.cast_succ]
      rw [← Ordinal.add_one_eq_succ, ← Ordinal.add_one_eq_succ]
      rw [mul_add, mul_one, add_assoc, add_assoc]; norm_num
    rw [h1, h2]
    exact MaxFun_le_MinFun_succ (η + ↑n) (η + 2 * ↑n) ih

/-- Tree argument: MaxFun(η) ≤ g for limit η with CBRank g = η. -/
private lemma MaxFun_le_limit_rank (η : Ordinal.{0}) (_hη : η < omega1)
    (_hlam : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (_hgc : Continuous g) (_hg : ScatteredFun g)
    (_hrank : CBRank g = η) :
    ContinuouslyReduces (MaxFun η) g := by
  sorry

/-- **Theorem (JSLgeneralstructure). General Structure Theorem.** -/
theorem general_structure_theorem
    (A B : Set Baire)
    (f : A → Baire) (g : B → Baire)
    (hf : ScatteredFun f) (hg : ScatteredFun g)
    (hfc : Continuous f) (hgc : Continuous g)
    (η : Ordinal.{0})
    (hη : η < omega1)
    (hlam : Order.IsSuccLimit η ∨ η = 0) :
      ((CBRank g = η ∧ CBRank f ≤ CBRank g)
        → ContinuouslyReduces f g)
      ∧
      (∀ n : ℕ, (CBRank f = η + ↑n ∧ CBRank g ≥ η + 2 * ↑n + 1)
        → ContinuouslyReduces f g) := by
  constructor
  · -- Item 1
    intro ⟨hg_rank, hf_le⟩
    have hf_le_η : CBRank f ≤ η := hg_rank ▸ hf_le
    rcases hlam with hlam_limit | hlam_zero
    · -- η is limit
      have hf_max : ContinuouslyReduces f (MaxFun η) :=
        (maxFun_is_maximum' η hη).1 f hfc hf
          (fun β hβ => cblevel_empty_of_le f hf β (hf_le_η.trans hβ))
      exact hf_max.trans (MaxFun_le_limit_rank η hη hlam_limit B g hgc hg hg_rank)
    · -- η = 0
      subst hlam_zero
      have hfr : CBRank f = 0 := nonpos_iff_eq_zero.mp (hg_rank ▸ hf_le)
      have : IsEmpty ↥A :=
        isEmpty_of_CBLevel_zero_empty f (cblevel_empty_of_le f hf 0 hfr.le)
      exact continuouslyReduces_of_empty f g
  · -- Item 2
    intro n ⟨hf_rank, hg_ge⟩
    have hηn_lt : η + ↑n < omega1 := omega1_add_nat η hη n
    -- f ≤ MaxFun(η + n)
    have hf_max : ContinuouslyReduces f (MaxFun (η + ↑n)) :=
      (maxFun_is_maximum' (η + ↑n) hηn_lt).1 f hfc hf
        (fun β hβ => cblevel_empty_of_le f hf β (hf_rank ▸ hβ))
    -- MaxFun(η + n) ≤ MinFun(η + 2n)
    have hmax_min := MaxFun_le_MinFun η hη hlam n
    -- MinFun(η + 2n) ≤ g
    have h_cast : (↑(2 * n) : Ordinal.{0}) = 2 * ↑n := by push_cast; ring
    have h2n_lt : η + ↑(2 * n) < omega1 := omega1_add_nat η hη (2 * n)
    have h2n_lt_rank : η + ↑(2 * n) < CBRank g := by
      rw [h_cast]; exact lt_of_lt_of_le (Order.lt_succ _) hg_ge
    have hmin_g : ContinuouslyReduces (MinFun (η + ↑(2 * n))) g :=
      minFun_is_minimum (η + ↑(2 * n)) h2n_lt B g hgc hg
        (CBLevel_nonempty_below_rank g hg (η + ↑(2 * n)) h2n_lt_rank)
    -- Rewrite to match types
    have hmax_min' : ContinuouslyReduces (MaxFun (η + ↑n)) (MinFun (η + ↑(2 * n))) := by
      rwa [h_cast]
    exact (hf_max.trans hmax_min').trans hmin_g

end
