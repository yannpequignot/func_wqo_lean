import RequestProject.CenteredMemo.Theorems

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Formalization of `5_precise_struct_memo.tex` — Definitions

This file formalizes the definitions from Chapter 5 (Precise Structure) of the memoir
on continuous reducibility between functions on the Baire space.

## Main definitions

* `WedgeDomComponent` — components of the domain of the wedge operation
* `WedgeDom` — domain of the wedge operation
* `WedgeFun` — the wedge operation `⋁(f₀, …, fₖ | f_{k+1})`
* `IsDominatedBy` — domination order on sets of functions
* `DominationEquiv` — domination equivalence of sets of functions
* `InScatteredClass` — membership in the class of scattered continuous functions
* `InCBLevel` — membership in a CB-rank level
* `FiniteGeneration` — the statement `FG(α)`
* `OmegaFun` — the omega operation `ω f`
-/

noncomputable section

/-!
## Section 1: The Wedge Operation (§5.1, Definition 5.1)

Given functions `(f_i)_{i ≤ k}` (the "verticals") and `f_{k+1}` (the "diagonal"),
the wedge `⋁(f₀, …, fₖ | f_{k+1})` is defined as follows.

**Domain:** `⊔_i A_i` where `A_i = pgl(dom f_i)` for `i ≤ k` and
`A_{k+1+i} = dom f_{k+1}` for all `i ∈ ℕ`.

**Codomain:** `pgl_j B_j` where `B_j = ⊔_{i ≤ k+1} im f_i` for all `j`.

**Action:**
- `f((i) ⌢ 0^ω) = 0^ω` if `i ≤ k`
- `f((i) ⌢ (0)^j ⌢ (1) ⌢ x) = (0)^j ⌢ (1) ⌢ (i) ⌢ f_i(x)` if `i ≤ k`
- `f((k+1+i) ⌢ x) = (0)^i ⌢ (1) ⌢ (k+1) ⌢ f_{k+1}(x)`
-/

/-- The domain components of the wedge operation: for `i ≤ k`, the `i`-th component is
`pgl(dom f_i)`; for `i = k+1+n`, it is `dom f_{k+1}`.
Overall domain is the (infinite) gluing `⊔_i A_i`. -/
def WedgeDomComponent (k : ℕ) (A_vert : Fin (k + 1) → Set (ℕ → ℕ))
    (A_diag : Set (ℕ → ℕ)) : ℕ → Set (ℕ → ℕ) :=
  fun i =>
    if h : i ≤ k then
      PointedGluingSet (fun _ => A_vert ⟨i, by omega⟩)
    else
      A_diag

/-- The domain of the wedge: the gluing of all components. -/
def WedgeDom (k : ℕ) (A_vert : Fin (k + 1) → Set (ℕ → ℕ))
    (A_diag : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  GluingSet (WedgeDomComponent k A_vert A_diag)

/-- The wedge function `⋁(f₀, …, fₖ | f_{k+1})`.

Given:
- `k : ℕ` — number of "vertical" functions minus 1
- `f_vert : Fin (k+1) → (ℕ → ℕ) → (ℕ → ℕ)` — the vertical functions
- `f_diag : (ℕ → ℕ) → (ℕ → ℕ)` — the diagonal function

Produces a function on the Baire space implementing:
- `(i) ⌢ 0^ω ↦ 0^ω` for `i ≤ k`
- `(i) ⌢ (0)^j ⌢ (1) ⌢ x ↦ (0)^j ⌢ (1) ⌢ (i) ⌢ f_i(x)` for `i ≤ k`
- `(k+1+i) ⌢ x ↦ (0)^i ⌢ (1) ⌢ (k+1) ⌢ f_{k+1}(x)` -/
def WedgeFun (k : ℕ)
    (f_vert : Fin (k + 1) → ((ℕ → ℕ) → (ℕ → ℕ)))
    (f_diag : (ℕ → ℕ) → (ℕ → ℕ)) :
    (ℕ → ℕ) → (ℕ → ℕ) :=
  fun x =>
    let head := x 0  -- first coordinate selects the component
    let tail := unprepend x  -- remaining coordinates
    if h : head ≤ k then
      -- Vertical component i = head
      -- tail lives in pgl(dom f_{head})
      -- Check if tail = 0^ω
      if tail = zeroStream then
        zeroStream
      else
        -- tail = (0)^j ⌢ (1) ⌢ y for some j, y
        -- Output: (0)^j ⌢ (1) ⌢ (head) ⌢ f_{head}(y)
        let j := firstNonzero tail
        let y := stripZerosOne j tail
        prependZerosOne j (prepend head (f_vert ⟨head, by omega⟩ y))
    else
      -- Diagonal component: head = k + 1 + i for i = head - (k+1)
      let i := head - (k + 1)
      -- Output: (0)^i ⌢ (1) ⌢ (k+1) ⌢ f_{k+1}(tail)
      prependZerosOne i (prepend (k + 1) (f_diag tail))

/-!
## Domination Order on Sets of Functions (used in Corollary 5.6)
-/

/-- A set of functions `F` is *dominated* by a set of functions `G` if for every
`f ∈ F` there exists `g ∈ G` with `f ≤ g`. -/
def IsDominatedBy {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (F : Set (X → Y)) (G : Set (X' → Y')) : Prop :=
  ∀ f ∈ F, ∃ g ∈ G, ContinuouslyReduces f g

/-- Two sets of functions are *domination-equivalent* if each dominates the other. -/
def DominationEquiv {X Y X' Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y']
    (F : Set (X → Y)) (G : Set (X' → Y')) : Prop :=
  IsDominatedBy F G ∧ IsDominatedBy G F

/-!
## Scattered class and CB-level predicates
-/

/-- Predicate: a function `f` belongs to the class of
*scattered continuous functions* `𝒞`. -/
def InScatteredClass {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ScatteredFun f ∧ Continuous f

/-- Predicate: a function `f` belongs to the CB-rank level `𝒞_α`. -/
def InCBLevel {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (α : Ordinal.{0}) : Prop :=
  InScatteredClass f ∧ CBRank f = α

/-- Predicate: a function `f` belongs to `𝒞_{≤α}`. -/
def InCBLevelLE {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (α : Ordinal.{0}) : Prop :=
  InScatteredClass f ∧ CBRank f ≤ α

/-- Predicate: a function `f` belongs to `𝒞_{<α}`. -/
def InCBLevelLT {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (α : Ordinal.{0}) : Prop :=
  InScatteredClass f ∧ CBRank f < α

/-- Predicate: a function `f` belongs to `𝒞_{[λ,α]}`. -/
def InCBLevelInterval {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (lam α : Ordinal.{0}) : Prop :=
  InScatteredClass f ∧ lam ≤ CBRank f ∧ CBRank f ≤ α

/-!
## Finite Generation

`FG(α)`: Every function in `𝒞_α` is continuously equivalent to a finite gluing
of generators at level `α`.
-/

/-- `FiniteGeneration α`: Every function in `𝒞_α` is continuously equivalent to
a finite gluing of functions from the generator set `𝒢(α)`.

This is the statement `FG(α)` from the text. We express it by asserting the existence
of finitely many functions on the Baire space (each in `𝒞_α`) whose gluing is
continuously equivalent to `f`. -/
def FiniteGeneration (α : Ordinal.{0}) : Prop :=
  ∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y),
    InCBLevel f α →
    ∃ (n : ℕ) (g : Fin n → ((ℕ → ℕ) → (ℕ → ℕ))),
      -- each g_i is in 𝒞_{≤α} (a generator)
      (∀ i, InCBLevelLE (g i) α) ∧
      -- f is continuously equivalent to a finite gluing of the g_i
      -- (here we express this using the gluing with the function that
      -- maps component j to g_{j mod n})
      ContinuouslyEquiv f
        (fun (x : ℕ → ℕ) =>
          let j := x 0
          if h : j < n then prepend j (g ⟨j, h⟩ (unprepend x))
          else x)

/-- `FG_below α`: `FG(β)` holds for all `β < α`. -/
def FiniteGeneration_below (α : Ordinal.{0}) : Prop :=
  ∀ β : Ordinal.{0}, β < α → FiniteGeneration β

/-- `FG_le α`: `FG(β)` holds for all `β ≤ α`. -/
def FiniteGeneration_le (α : Ordinal.{0}) : Prop :=
  ∀ β : Ordinal.{0}, β ≤ α → FiniteGeneration β

/-!
## Omega operation on functions

`ω f` is the infinite gluing `⊔_{n ∈ ℕ} f`, i.e., countably many disjoint copies of `f`.
-/

/-- `OmegaFun f` is the infinite gluing of countably many copies of `f`:
`ω f = ⊔_{n ∈ ℕ} f`, mapping `(n) ⌢ x ↦ (n) ⌢ f(x)`. -/
def OmegaFun (f : (ℕ → ℕ) → (ℕ → ℕ)) : (ℕ → ℕ) → (ℕ → ℕ) :=
  fun x => prepend (x 0) (f (unprepend x))

end
