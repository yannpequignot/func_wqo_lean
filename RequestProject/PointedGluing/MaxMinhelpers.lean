import Mathlib
import RequestProject.IntroMemo
import RequestProject.PrelimMemo.Basic
import RequestProject.PrelimMemo.Scattered
import RequestProject.PrelimMemo.Gluing
import RequestProject.PointedGluing.Defs

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
MaxFun α is scattered with CB-rank ≤ α (in fact equal)
-/
lemma maxfun_is_scatter_leq_α (α : Ordinal.{0}) (hα : α < omega1) : ScatteredFun (MaxFun α) ∧
    (∀ β : Ordinal.{0}, α < β → CBLevel (MaxFun α) β = ∅):= by
    sorry

/-
MinFun α is scattered with CB-rank ≤ α+1 (in fact equal)
-/
lemma minfun_is_scatter_leq_succ_α (α : Ordinal.{0}) (hα : α < omega1) : ScatteredFun (MinFun α) ∧
    (∀ β : Ordinal.{0}, Order.succ α < β → CBLevel (MinFun α) β = ∅):= by
    sorry

lemma MaxFun_monotone (α β: Ordinal.{0})
    (hα : α < omega1) (hβ : β < omega1)
    (hl: α ≤ β):
    ContinuouslyReduces (MaxFun α) (MaxFun β):= by
    sorry
