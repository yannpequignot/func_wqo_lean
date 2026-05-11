
import Mathlib
import RequestProject.Bqo.Ramsey
open Set

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Classical


/-
TwoBQO.lean
===========

A Lean 4 / Mathlib formalization of 2-better-quasi-orders (2-BQO).

Goals of this file (following Pequignot, EMS Surveys 2017):
  (A) Definition of 2-BQO via bad pair-sequences on [ℕ]²
  (B) Ever pair-sequence restricts to either a bad or perfect pair-sequence
  (C) 2-BQO → WQO
  (D) ω₁ is 2-BQO
  (E) Finite products of 2-BQOs are 2-BQO
  (F) Sum of 2-BQOs along a 2-BQO is 2-BQO  (key theorem)
-/

/-!
## §2  Bad pair-sequences and 2-BQO
-/

/-- A **pair-sequence** in `α` assigns a value to every pair `(m, n)` with `m < n`. -/
abbrev PairSeq (α : Type*) := ∀ (m n : ℕ), m < n → α

def restrictPairSeq {α : Type*} (f : PairSeq α) (e : ℕ → ℕ) (he_mono : StrictMono e) :
    PairSeq α :=
  fun m n hmn => f (e m) (e n) (he_mono hmn)

/-- A pair-sequence `f` is **bad** for `r` if:
    for all `m < n < l`, `f(m,n)` and `f(n,l)` are not `r`-related.

    This is the specialisation of Pequignot's "bad super-sequence" to the
    rank-2 front `[ℕ]²`. -/
def BadPairSeq {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ (m n l : ℕ), ∀ (hmn : m < n) (hnl : n < l),
    ¬ r (f m n hmn) (f n l hnl)

def PerfectPairSeq {α : Type*} (r : α → α → Prop) (f : PairSeq α) : Prop :=
  ∀ (m n l : ℕ), ∀ (hmn : m < n) (hnl : n < l),
    r (f m n hmn) (f n l hnl)


/-- `r` is **2-BQO** if there is no bad pair-sequence for `r`. -/
def TwoBQO_n {α : Type*} (r : α → α → Prop) : Prop :=
  ¬ ∃ f : PairSeq α, BadPairSeq r f

def TwoBQO {α : Type*} (r : α → α → Prop) : Prop :=
  ∀ (f : PairSeq α), ∃ m n l : ℕ, ∃ (hmn : m < n) (hnl : n < l),
    r (f m n hmn) (f n l hnl)

theorem isTwoBQO_iff {α : Type*} (r : α → α → Prop) :
    TwoBQO r ↔ TwoBQO_n r := by
  simp [TwoBQO_n, BadPairSeq, not_exists, not_forall]
  exact Iff.symm (Eq.to_iff rfl)

theorem perfect_or_bad {α : Type*} (r : α → α → Prop)
    (f : PairSeq α) : ∃ e : ℕ → ℕ, ∃ (he_mono : StrictMono e),
    (PerfectPairSeq r (restrictPairSeq f e he_mono)
     ∨ BadPairSeq r (restrictPairSeq f e he_mono)) := by
  obtain ⟨e, he_mono, k, hk⟩ := @infinite_ramsey_triples Bool inferInstance
    (fun h i j (hs : h < i ∧ i < j) => decide (r (f h i hs.1) (f i j hs.2)))
  refine ⟨e, he_mono, ?_⟩
  rcases Bool.eq_false_or_eq_true k with hk_false | hk_true
  · left
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_false] at h_color
    simpa [decide_eq_false_iff_not] using h_color
  · right
    intro h i j hs ht
    have h_color := hk h i j ⟨hs, ht⟩
    rw [hk_true] at h_color
    simpa [decide_eq_true_eq] using h_color

/-!
## §3  2-BQO implies WQO
-/

/-- **2-BQO implies WQO** (Pequignot, Proposition 2.2).

**Proof:** Given a sequence `g : ℕ → α`, apply 2-BQO to the pair-sequence
`(m, n, _) ↦ g m`. A good triple `m < n < l` yields `r (g m) (g n)`. -/
theorem TwoBQO.wellQuasiOrdered {α : Type*} {r : α → α → Prop}
    (h : TwoBQO r) : WellQuasiOrdered r := by
  rw [WellQuasiOrdered]
  intro g
  obtain ⟨m, n, _l, hmn, _hnl, hrel⟩ := h (fun m _n _hmn => g m)
  exact ⟨m, n, hmn, hrel⟩

/-!
## §4  Well-orders are 2-BQO
-/

/-- **Well-orders are 2-BQO.**

**Proof:** if `f` is bad for a well-order `<`, the sequence `n ↦ f(n, n+1)`
is strictly decreasing, contradicting well-foundedness. -/
theorem TwoBQO.of_wellFoundedLT {α : Type*} [LinearOrder α] [WellFoundedLT α] :
    TwoBQO (α := α) (· ≤ ·) := by
  rw [isTwoBQO_iff]
  intro ⟨f, hbad⟩
  have hstrict : ∀ n, f (n+1) (n+2) (Nat.lt_succ_self _)
                        < f n (n+1) (Nat.lt_succ_self _) :=
    fun n => not_le.mp
      (hbad n (n+1) (n+2) (Nat.lt_succ_self n) (Nat.lt_succ_self (n+1)))
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· < ·))
    (fun n => f n (n+1) (Nat.lt_succ_self n))
  exact hn (hstrict n)

/-!
## §5  ω₁ is 2-BQO

The ordinal ω₁ is 2-BQO because it is a well-order.
-/

/-- `ω₁` as a countable ordinal. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord

/-- **ω₁ is 2-BQO** with respect to `≤`. -/
theorem Ordinal.omega1_le_isTwoBQO :
    TwoBQO (α := Set.Iio omega1) (· ≤ ·) :=
  TwoBQO.of_wellFoundedLT

/-!
## §6  Closure properties

### 6.1  Monotone preimage (downward closure)
-/

/-- 2-BQO is closed under monotone preimage: if `φ : β → α` is monotone
and `r` on `α` is 2-BQO, then the pullback of `r` along `φ` is 2-BQO. -/
theorem TwoBQO.comap {α β : Type*} {r : α → α → Prop}
    (h : TwoBQO r) (φ : β → α) :
    TwoBQO (fun a b => r (φ a) (φ b)) := by
  rw [isTwoBQO_iff] at h ⊢
  intro ⟨f, hbad⟩
  exact h ⟨fun m n hmn => φ (f m n hmn),
    fun m n l hmn hnl hrel => hbad m n l hmn hnl hrel⟩

/-- **Subtype closure.** -/
theorem IsTwoBQO.subtype {α : Type*} {r : α → α → Prop}
    (h : TwoBQO r) (p : α → Prop) :
    TwoBQO (fun a b : Subtype p => r a.val b.val) :=
  h.comap Subtype.val



/-!
### 6.2  Finite products (Dickson's lemma for 2-BQO)

**Theorem:** If `r` and `s` are 2-BQO then the componentwise product
`r × s` on `α × β` is 2-BQO.

**Proof:** Let `f : PairSeq (α × β)` be bad for `r × s`.
Write `f₁(m,n) = (f m n).1` and `f₂(m,n) = (f m n).2`.

Step 1: Apply RT² to the colouring of pairs:
  colour `(m,n)` by 0 if `r (f₁ m n) (f₁ n ?)` ... wait, RT² colours
  by a fixed colour, but we need to compare consecutive values.

Actually the cleanest argument does NOT need RT²:

If `f` is bad for `r × s`, then `f₁ = (·).1 ∘ f` is bad for `r`:
- Suppose `f₁` has a good triple `m < n < l`: `r (f₁ m n) (f₁ n l)`.
- Since `f` is bad: `¬ (r (f₁ m n) (f₁ n l) ∧ s (f₂ m n) (f₂ n l))`.
- So `¬ s (f₂ m n) (f₂ n l)`.

So the triple that's good for `r` is bad for `s`. We need to find a pair-
sequence that is globally bad for `s`, not just bad at one triple.

This is where RT² enters: apply it to colour pairs by whether r holds.
Get an infinite monochromatic set.
- If r always holds: then for s, the restricted f₂ is bad → contradiction.
- If r never holds: then f₁ is bad → contradiction with r being 2-BQO.
-/

/-- **Product closure** (Dickson's lemma for 2-BQO).

If `r` on `α` and `s` on `β` are 2-BQO, then the componentwise product
`fun (a₁,b₁) (a₂,b₂) => r a₁ a₂ ∧ s b₁ b₂` on `α × β` is 2-BQO. -/
theorem TwoBQO.prod {α β : Type*} {r : α → α → Prop} {s : β → β → Prop}
    (hr : TwoBQO r) (hs : TwoBQO s) :
    TwoBQO (fun x y : α × β => r x.1 y.1 ∧ s x.2 y.2) := by
  rw [isTwoBQO_iff] at hr hs ⊢
  intro ⟨f, hbad⟩
  -- f₁ : PairSeq α  is the first-coordinate projection
  let f₁ : PairSeq α := fun m n h => (f m n h).1
  -- Apply perfect_or_bad to f₁ under r
  obtain ⟨e₁, he₁, hperf₁ | hbad₁⟩ := perfect_or_bad r f₁
  · -- f₁ is perfect along e₁: r holds on every consecutive pair.
    -- Look at the second coordinate of f restricted to e₁.
    let f₂ : PairSeq β := fun m n h => (restrictPairSeq f e₁ he₁ m n h).2
    -- Apply perfect_or_bad to f₂ under s
    obtain ⟨e₂, he₂, hperf₂ | hbad₂⟩ := perfect_or_bad s f₂
    · -- Both coordinates perfect: derive a contradiction from hbad.
      -- At the triple (e₁(e₂ 0), e₁(e₂ 1), e₁(e₂ 2)), r and s both hold,
      -- but hbad says the product never holds.
      exact hbad (e₁ (e₂ 0)) (e₁ (e₂ 1)) (e₁ (e₂ 2))
        (he₁ (he₂ (by norm_num : 0 < 1))) (he₁ (he₂ (by norm_num : 1 < 2)))
        ⟨hperf₁ (e₂ 0) (e₂ 1) (e₂ 2) (he₂ (by norm_num : 0 < 1)) (he₂ (by norm_num : 1 < 2)),
         hperf₂ 0 1 2 (by norm_num : 0 < 1) (by norm_num : 1 < 2)⟩
    · -- f₂ restricted to e₂ is bad for s: contradicts hs
      exact hs ⟨restrictPairSeq f₂ e₂ he₂, hbad₂⟩
  · -- f₁ restricted to e₁ is bad for r: contradicts hr
    exact hr ⟨restrictPairSeq f₁ e₁ he₁, hbad₁⟩

/-- **Iterated finite product.** For a Fintype index `ι`, the product
`∀ i, α i` with pointwise quasi-order is 2-BQO when each component is. -/
theorem TwoBQO.pi {ι : Type*} [Fintype ι] {α : ι → Type*}
    {r : (i : ι) → α i → α i → Prop}
    (h : ∀ i, TwoBQO (r i)) :
    TwoBQO (fun f g : ∀ i, α i => ∀ i, r i (f i) (g i)) := by
  sorry
/-!
### 6.3  Sum along a 2-BQO (the main closure theorem)

**Setup:** Given a quasi-order `r` on `ι` and quasi-orders `s i` on `α i`,
the **sum** `Σᵢ αᵢ` is ordered by:
  `(i, x) ≤ (j, y)` iff `r i j ∧ i ≠ j`  (strictly above)
  or  `i = j ∧ s i x y`                   (same fibre).

This is Pequignot's Proposition 2.4(iii) lifted to 2-BQO.

**Proof:**
Suppose `f : PairSeq (Σ i, α i)` is bad for the sum order.
Write `idx(m,n) = (f m n).1 : ι`.

Apply RT² to the colouring of pairs `(m,n)` by `idx(m,n)` — but `ι` may be
infinite. Instead, apply 2-BQO of `r` directly to the pair-sequence
`(m,n) ↦ idx(m,n)`: since `r` is 2-BQO, there exist `m < n < l` with
`r (idx m n) (idx n l)`.

Case 1: `idx(m,n) ≠ idx(n,l)`. Then the sum order holds (left disjunct).
  But `f` is bad: contradiction.

Case 2: `idx(m,n) = idx(n,l)` (call it `i`). Then the sum order requires
  `s i (f m n).2 (h ▸ (f n l).2)`. Since `f` is bad, this fails.
  So the pair-sequence `(m,n) ↦ (f m n).2` (in `α i`, along pairs with
  both index equal to `i`) is bad for `s i`.
  To make this precise, we need an infinite set of pairs where the index
  is always `i`, for which we use RT² on the index pair-sequence.
  Then `hs i` gives a contradiction.
-/

/-- The **lexicographic sum order along a wellorder** on `Σ i, α i`:
    `(i,x) ≤ (j,y)` iff `i` is strictly below `j` in `r`, or `i = j`
    and `x ≤ y` in `s i`. -/
def LexSumRel {α : Type*} [LinearOrder α] [WellFoundedLT α]
    (s : α → Type*) (t : ∀ i, s i → s i → Prop) :
    (Σ i, s i) → (Σ i, s i) → Prop
  | ⟨i, x⟩, ⟨j, y⟩ =>
      (i < j) ∨
      ∃ h : i = j, t i x (h ▸ y)

/-- **Sum theorem for 2-BQO.**

If `r` on `ι` is 2-BQO and each `s i` on `α i` is 2-BQO, then
`Σ i, α i` with `LexSumRel r s` is 2-BQO. -/
theorem TwoBQO.lexSigma
    {α : Type*} [LinearOrder α] [WellFoundedLT α]
    (s : α → Type*)
    (t : ∀ i, s i → s i → Prop)
    (hs : ∀ i, TwoBQO (t i)) :
    TwoBQO (LexSumRel s t) := by
  sorry
