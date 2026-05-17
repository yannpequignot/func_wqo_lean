import RequestProject.PointedGluing.Defs
import Mathlib

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
# Ordinal Arithmetic Helpers

Helper lemmas about ordinal decomposition and cofinal sequences used in the
General Structure Theorem.

## Main results

* `limit_add_nat_lt` — adding a finite number to an ordinal below a limit stays below
* `ordinal_limit_nat_decomposition` — every ordinal decomposes as limit + ℕ
* `cofinalSeq_eventually_ge` — cofinal sequences eventually exceed any target
-/

/-- For limit η, adding a finite natural number m stays below η. -/
lemma limit_add_nat_lt (η : Ordinal.{0}) (hlim : Order.IsSuccLimit η) (_hne : η ≠ 0)
    (α : Ordinal.{0}) (hα : α < η) (m : ℕ) :
    α + ↑m < η := by
  induction' m with m ih
  · simpa using hα
  · convert hlim.succ_lt ih using 1
    simp +decide [Ordinal.add_succ]

/-- Every ordinal can be decomposed as α' + m where α' is limit or 0 and m ∈ ℕ. -/
lemma ordinal_limit_nat_decomposition (α : Ordinal.{0}) :
    ∃ (α' : Ordinal.{0}) (m : ℕ),
      (Order.IsSuccLimit α' ∨ α' = 0) ∧ α = α' + ↑m := by
  by_contra! h_contra
  induction' α using Ordinal.induction with α ih
  by_cases hα : Order.IsSuccLimit α ∨ α = 0
  · exact h_contra α 0 hα (by simp +decide)
  · obtain ⟨β, rfl⟩ : ∃ β, α = Order.succ β := by
      simp_all +decide [Order.IsSuccLimit]
      simp_all +decide [Order.IsSuccPrelimit]
      exact Exists.elim (hα.1 hα.2) fun x hx => ⟨x, hx.succ_eq.symm⟩
    specialize ih β (Order.lt_succ β) ; simp_all +decide
    obtain ⟨α', hα', m, hm⟩ := ih; specialize h_contra α' (m + 1) ; simp_all +decide
    exact h_contra (by rw [Ordinal.add_succ])

/-- For every ordinal β < η (limit), there exists n such that cofinalSeq η n ≥ β. -/
lemma cofinalSeq_eventually_ge (η : Ordinal.{0}) (hη : η < omega1)
    (hlim : Order.IsSuccLimit η) (hne : η ≠ 0)
    (β : Ordinal.{0}) (hβ : β < η) :
    ∃ n : ℕ, β ≤ cofinalSeq η n := by
  have h_surj : Function.Surjective (fun n => ⟨cofinalSeq η n, cofinalSeq_lt η hlim hne n⟩ : ℕ → Iio η) := by
    convert enumBelow_surj η hη hne using 1
    unfold cofinalSeq; aesop
  cases' h_surj ⟨β, hβ⟩ with n hn ; use n ; aesop

end
