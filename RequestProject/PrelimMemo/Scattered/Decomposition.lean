import RequestProject.PrelimMemo.Scattered.NonScattered
import RequestProject.PrelimMemo.Gluing

open scoped Topology
open Set Function TopologicalSpace

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Simple Functions, First Reduction, and Decomposition Lemma

## Main definitions

* `SimpleFun` — a function is simple if it has CB-degree 1

## Main results

* `first_reduction_theorem` — Theorem 2.12
* `decomposition_lemma_baire` — Lemma 2.15
-/

section SimpleFunctions

/-- A function is simple if it is scattered and has CB-degree 1: the last CB-level
maps to a single point. -/
def SimpleFun {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ScatteredFun f ∧
  ∃ α : Ordinal.{0},
    (CBLevel f α).Nonempty ∧
    CBLevel f (Order.succ α) = ∅ ∧
    ∃ y, ∀ x ∈ CBLevel f α, f x = y

end SimpleFunctions

section FirstReductionTheorem

/-!
## Theorem 2.12 (FirststepforBQOthm)

Every continuous function from a zero-dimensional separable metrizable space to a
metrizable space is either scattered, equivalent to `id_ℚ`, or equivalent to `id_{ℕ→ℕ}`.
-/

/-- **First Reduction Theorem.** Every continuous function from a zero-dimensional
separable metrizable space to a metrizable space is either scattered, or continuously
equivalent to `id_ℚ`, or continuously equivalent to `id_{ℕ → ℕ}`.

This theorem combines deep results: the Cantor scheme construction (Theorem 2.5),
universality results for `ℚ` and the Baire space `ℕ → ℕ`, and the Perfect Function
Property. -/
theorem first_reduction_theorem
    {X Y : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y]
    {f : X → Y} (hf : Continuous f) :
    ScatteredFun f ∨
    ContinuouslyEquiv f (@id ℚ) ∨
    ContinuouslyEquiv f (@id (ℕ → ℕ)) := by
  sorry

end FirstReductionTheorem

section ZeroDimAndDisjointUnion

/-!
## Proposition 2.14 (0dimanddisjointunion)

Let `f` be a function with separable metrizable 0-dimensional domain and `F` a class
of functions. Then `f` is locally `F` if and only if `f = ⨆ᵢ fᵢ` for some sequence of
functions `(fᵢ) ⊆ F`.

**Locally F** means: for every `x ∈ dom(f)`, there exists a clopen neighborhood `C ∋ x`
such that `f|_C ∈ F`.
-/

/-- A function `f : X → Y` is *locally in class `F`* if every point of `X` has a
clopen neighborhood on which `f` restricted is in `F`.
Here `F` is a predicate on functions from subtypes of `X` to `Y`. -/
def IsLocallyInClass {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (F : (S : Set X) → (S → Y) → Prop) : Prop :=
  ∀ x : X, ∃ C : Set X, IsClopen C ∧ x ∈ C ∧ F C (fun a => f a.val)

/-!
### Proposition 2.14 (0dimanddisjointunion)

For a function `f` with domain a subspace of the Baire space and `F` a class of
functions, `f` is locally `F` if and only if `f` is a disjoint union of functions
in `F` over a clopen partition.

The forward direction is the interesting one: in a 0-dimensional separable metrizable
space, every open cover can be refined to a clopen partition, using the tree structure
of the Baire space. The backward direction is trivial since each piece of a clopen
partition is itself clopen.
-/

/-- A function `f : X → Y` is a disjoint union of the sequence `(fᵢ)` over a clopen
partition `(Aᵢ)` of `X`. (Duplicated from Gluing.lean to avoid circular import.) -/
def IsDisjointUnion' {X Y : Type*} [TopologicalSpace X]
    {I : Type*} (f : X → Y) (A : I → Set X) (fi : ∀ i, A i → Y) : Prop :=
  (∀ i, IsClopen (A i)) ∧
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
  (⋃ i, A i) = univ ∧
  (∀ i (x : A i), f x.val = fi i x)

/-
**Proposition 2.14 (0dimanddisjointunion).**
Backward direction: if `f` is a disjoint union of functions in `F`,
then `f` is locally in class `F`.
-/
theorem disjoint_union_implies_locally
    {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (F : (S : Set X) → (S → Y) → Prop)
    {I : Type*} (P : I → Set X) (fi : ∀ i, P i → Y)
    (hdu : IsDisjointUnion' f P fi)
    (hF : ∀ i, F (P i) (fi i)) :
    IsLocallyInClass f F := by
  -- For any $x \in X$, there exists $i \in I$ such that $x \in P_i$.
  have h_exists_i : ∀ x : X, ∃ i : I, x ∈ P i := by
    exact fun x => by simpa using Set.ext_iff.mp hdu.2.2.1 x;
  intro x
  obtain ⟨i, hi⟩ := h_exists_i x
  use P i;
  exact ⟨ hdu.1 i, hi, by convert hF i using 1; ext a; exact hdu.2.2.2 i a ▸ rfl ⟩

/-
**Proposition 2.14 (0dimanddisjointunion).**
Forward direction for Baire space subspaces:
if `f : A → Baire` with `A ⊆ Baire` is locally in class `F`,
then `f` is a disjoint union of functions in `F`.

Note: The proof in the original paper uses the tree structure of Baire space
and minimal prefixes. It implicitly requires `F` to be closed under restriction
to clopen subsets (captured by `hF_restrict`). This is satisfied by all standard
classes (simple, scattered with rank ≤ α, etc.).
-/
theorem locally_implies_disjoint_union_baire
    {A : Set Baire}
    (f : A → Baire)
    (F : (S : Set A) → (S → Baire) → Prop)
    (hloc : IsLocallyInClass f F)
    (hF_restrict : ∀ (C D : Set A), D ⊆ C → IsClopen D →
      F C (fun a => f a.val) → F D (fun a => f a.val)) :
    ∃ (I : Type) (P : I → Set A) (fi : ∀ i, P i → Baire),
      IsDisjointUnion' f P fi ∧ ∀ i, F (P i) (fi i) := by
  choose C hC hc using hloc;
  -- use Lindelof property to get a countable subcover
  obtain ⟨I, hI⟩ : ∃ I : Set A, Set.Countable I ∧ ⋃ x ∈ I, C x = Set.univ := by
    have h_countable_subcover : IsLindelof (Set.univ : Set A) := by
      exact isLindelof_univ
    have := h_countable_subcover.elim_countable_subcover ( fun x => C x );
    exact Exists.elim ( this ( fun x => ( hC x ).isOpen ) ( fun x _ => Set.mem_iUnion_of_mem x ( hc x |>.1 ) ) ) fun r hr => ⟨ r, hr.1, Set.Subset.antisymm ( Set.subset_univ _ ) hr.2 ⟩;
  have := hI.1.exists_eq_range;
  by_cases hI_empty : I.Nonempty;
  · obtain ⟨g, hg⟩ : ∃ g : ℕ → A, I = Set.range g := by
      exact this hI_empty;
    refine' ⟨ ℕ, fun n => disjointed ( fun n => C ( g n ) ) n, fun n => fun a => f a.val, _, _ ⟩ <;> simp_all +decide [ IsDisjointUnion' ];
    · refine' ⟨ _, _, _ ⟩;
      · exact fun i => disjointed_clopen (fun n => C (g n)) (fun n => hC (↑(g n)) (g n).property) i;
      · exact fun i j hij => disjoint_disjointed _ hij;
      · convert hI.2 using 1;
        exact iUnion_disjointed;
    · intro n;
      apply hF_restrict;
      exact disjointed_subset _ _;
      · exact disjointed_clopen _ ( fun n => hC _ _ ) _;
      · exact hc _ _ |>.2;
  · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hI_empty ];
    simp_all +decide [ IsDisjointUnion' ];
    exact ⟨ PEmpty, fun _ => ∅, by aesop ⟩

end ZeroDimAndDisjointUnion

/-- Corollary \label{CBrankofclopenunion}
Let $f$ be a scattered function and $(A_i)_{i\in I}$ be an open covering of $\dom(f)$ for some set $I$.
Then $\CB(f)=\sup_{i\in I}\CB(f\restr{A_i})$.
-/
theorem cb_rank_of_clopen_union {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (I : Type*) (A : I → Set X)
    (h_cover : (⋃ i, A i) = Set.univ)
    (h_clopen : ∀ i, IsClopen (A i)):
    CBRank f = ⨆ i, CBRank (fun (x : A i) => f x.val) := by
  -- let α = ⨆ i, CBRank (fun (x : A i) => f x.val)
  -- we prove CBRank f ≤ α and α ≤ CBRank f
  -- to show CBRank f ≤ α, we show CBLevel f α = ∅
  -- use isolatedLocus_open_restrict to get CBLevel (f|_{A i}) α = ∅ for all i
  -- use CBLevel_clopen_union_empty to get CBLevel f α = ∅,
  -- use CBLevel_eq_empty_at_rank to get CBRank f ≤ α
  -- to show α ≤ CBRank f, let β < α  and show CBLevel f β ≠ ∅
  -- then for some i we have CBLevel f β ⊇ CBLevel f β ∩ A i = CBLevel (f|_{A i}) β ≠ ∅
  -- since CBLevel f β ≠ ∅, we have CBRank f > β
  -- since β < α, we have CBRank f > β for all β < α
  -- therefore CBRank f ≥ α
  sorry

section DecompositionLemma

/-!
## Lemma 2.15 (DecompositionLemma)

Any scattered function from a zero-dimensional separable metrizable space is locally
simple.

The proof requires several ingredients:
1. **Clopen basis**: In a metrizable totally disconnected space, every open set
   containing a point has a clopen subset containing that point. This is de Groot's
   theorem: metrizable + totally disconnected → ultra-metrizable, and in an
   ultrametric space, all balls are clopen.
2. **CB analysis of restrictions**: The CB levels of a restriction relate to the
   CB levels of the original function.
3. **Local simplicity**: Using the CB rank of each point and the clopen basis,
   we find a clopen neighborhood on which the function is simple.
-/

/-- **Helper (clopen basis).** In a metrizable, separable, totally disconnected space,
every open set containing a point has a clopen subset containing that point.
This is a consequence of de Groot's theorem (metrizable + TD → ultra-metrizable)
and the fact that balls in an ultrametric space are clopen. -/
lemma exists_clopen_subset_of_open {X : Type*}
    [TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
    [TotallyDisconnectedSpace X]
    (x : X) (U : Set X) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  sorry

/-
In the Baire space, every open set containing a point has a clopen subset
containing that point. Follows from `baire_has_clopen_basis`.
-/
lemma baire_exists_clopen_subset_of_open
    (x : Baire) (U : Set Baire) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set Baire, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  obtain ⟨B, hB_basis, _, hB_clopen⟩ := baire_has_clopen_basis
  have hU_nhds : U ∈ nhds x := hU.mem_nhds hx
  rw [hB_basis.mem_nhds_iff] at hU_nhds
  obtain ⟨V, hV_in_B, hx_in_V, hV_sub_U⟩ := hU_nhds
  exact ⟨V, hB_clopen V hV_in_B, hx_in_V, hV_sub_U⟩

/-
In a subspace of the Baire space, every open set containing a point has a
clopen subset containing that point.
-/
lemma baire_subspace_exists_clopen_subset_of_open
    (A : Set Baire) (x : A) (U : Set A) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set A, IsClopen V ∧ x ∈ V ∧ V ⊆ U := by
  rcases hU with ⟨V, hV, rfl⟩;
  obtain ⟨W, hW⟩ : ∃ W : Set Baire, IsClopen W ∧ x.val ∈ W ∧ W ⊆ V := by
    exact baire_exists_clopen_subset_of_open x.val V hV hx;
  refine' ⟨ Subtype.val ⁻¹' W, _, _, _ ⟩;
  · exact hW.1.preimage continuous_subtype_val;
  · aesop;
  · exact Set.preimage_mono hW.2.2

/-- **Helper.** A constant function on a nonempty subtype is simple. -/
lemma simpleFun_const {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} (hU : U.Nonempty) (y : Y) :
    SimpleFun (fun (_ : U) => y) := by
  refine ⟨fun S hS => ⟨univ, isOpen_univ, ⟨hS.some, trivial, hS.some_mem⟩,
    fun _ _ _ _ => rfl⟩, 0, ⟨⟨hU.some, hU.some_mem⟩, by simp [CBLevel_zero]⟩, ?_, y, fun x _ => rfl⟩
  rw [CBLevel_succ', CBLevel_zero]
  ext ⟨z, hz⟩
  simp only [mem_diff, mem_univ, true_and, mem_empty_iff_false, iff_false, not_not]
  exact ⟨trivial, univ, isOpen_univ, trivial, fun _ _ => rfl⟩

/-
For a scattered function `f : A → Y`, the stabilizing set is nonempty
(the CB levels must stabilize since `A` is `Small.{0}`).
-/
lemma cb_stabilizing_set_nonempty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) :
    {α : Ordinal.{0} | CBLevel f α = CBLevel f (Order.succ α)}.Nonempty := by
  -- By definition of scattered, the CB level at sometimes stabilizes.
  have hCBStabilize : ∃ α, CBLevel f α = CBLevel f (Order.succ α) := by
    by_contra h
    push_neg at h
    --clauses t, 3, 0
    exact absurd ( CBLevel_strictAnti_of_ne f h ) ( by rintro ⟨ g, hg ⟩ ; exact not_injective_of_ordinal g hg );
  exact hCBStabilize

/-
For a scattered function, the CB level at CBRank is empty.
-/
lemma cbLevel_at_cbRank_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) :
    CBLevel f (CBRank f) = ∅ := by
  by_cases h_empty : (CBLevel f (CBRank f)).Nonempty;
  · have h_eq : CBLevel f (CBRank f) = CBLevel f (Order.succ (CBRank f)) := by
      exact csInf_mem ( cb_stabilizing_set_nonempty f hf );
    exact absurd h_eq ( ne_of_gt ( CBLevel_succ_ssubset_of_scattered f hf _ h_empty ) );
  · exact Set.not_nonempty_iff_eq_empty.mp h_empty

/-
The restriction of a scattered function to an open set is scattered.
-/
lemma scattered_restriction_open {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : ScatteredFun f)
    (U : Set X) (hU : IsOpen U) :
    ScatteredFun (f ∘ (Subtype.val : U → X)) := by
  intro S hS;
  obtain ⟨ x, hx ⟩ := hS;
  obtain ⟨ V, hV₁, hV₂, hV₃ ⟩ := hf ( Subtype.val '' S ) ⟨ _, Set.mem_image_of_mem _ hx ⟩;
  refine' ⟨ Subtype.val ⁻¹' V, _, _, _ ⟩ <;> simp_all +decide [ Set.Nonempty ];
  · exact hU.inter hV₁;
  · grind +extAll

/-
From x ∈ isolatedLocus f (CBLevel f β), get open U with f constant on
    U ∩ CBLevel f β and CBLevel f (succ β) ∩ U = ∅.
-/
lemma isolatedLocus_gives_simple_neighborhood {X Y : Type*}
    [TopologicalSpace X]
    {f : X → Y}
    (β : Ordinal.{0})
    (x : X)
    (hx : x ∈ isolatedLocus f (CBLevel f β)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      CBLevel f (Order.succ β) ∩ U = ∅ ∧
      ∀ y ∈ U ∩ CBLevel f β, f y = f x := by
  obtain ⟨U, hU_open, hx_in_U, hconst⟩ : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U ∩ (CBLevel f β), f y = f x := by
    exact hx.2;
  refine' ⟨ U, hU_open, hx_in_U, _, hconst ⟩;
  simp_all +decide [ Set.ext_iff, CBLevel_succ' ];
  intro y hy hy' hy''; contrapose! hy'; unfold isolatedLocus at *; aesop;

/-
Key lemma for decomposition: the restriction of f to a Baire-clopen set
    contained in the isolated locus neighborhood is simple.
-/
lemma restriction_to_clopen_is_simple
    {A : Set Baire}
    (f : A → Baire)
    (hf : ScatteredFun f)
    (β : Ordinal.{0})
    (V : Set Baire)
    (hV : IsClopen V)
    (hx_exists : ∃ x : A, (x : Baire) ∈ V ∧ x ∈ CBLevel f β)
    (hempty : CBLevel f (Order.succ β) ∩ (Subtype.val ⁻¹' V : Set A) = ∅)
    (hconst : ∃ y : Baire, ∀ z ∈ (Subtype.val ⁻¹' V : Set A) ∩ CBLevel f β, f z = y) :
    SimpleFun (f ∘ (Subtype.val : {a : A | (a : Baire) ∈ V} → A)) := by
  refine' ⟨ _, β, _, _, _ ⟩;
  · apply_rules [ ScatteredFun, scattered_restriction_open ];
    exact hV.isOpen.preimage continuous_subtype_val;
  · obtain ⟨ x, hx₁, hx₂ ⟩ := hx_exists; use ⟨ x, hx₁ ⟩ ; simp_all +decide [ local_cb_derivative ] ;
    have h_local : Subtype.val '' CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) β = (CBLevel f β) ∩ Subtype.val ⁻¹' V := by
      convert local_cb_derivative ( Subtype.val ⁻¹' V ) ( hV.2.preimage ( continuous_subtype_val ) ) β using 1;
      exact Pi.topologicalSpace;
    exact h_local.symm.subset ⟨ hx₂, hx₁ ⟩ |> fun ⟨ y, hy₁, hy₂ ⟩ => hy₂ ▸ hy₁;
  · have h_local_cb_derivative : Subtype.val '' CBLevel (f ∘ (Subtype.val : {a : A | a.val ∈ V} → A)) (Order.succ β) = CBLevel f (Order.succ β) ∩ Subtype.val ⁻¹' V := by
      apply local_cb_derivative;
      exact hV.isOpen.preimage continuous_subtype_val;
    aesop;
  · use hconst.choose;
    intro x hx;
    apply hconst.choose_spec;
    exact ⟨ x.2, local_cb_derivative _ ( show IsOpen ( Subtype.val ⁻¹' V ) from hV.isOpen.preimage continuous_subtype_val ) _ |>.subset ( Set.mem_image_of_mem _ hx ) |> fun h => h.1 ⟩

/-
**Decomposition Lemma.** Any scattered function from a zero-dimensional separable
metrizable space is locally simple: around each point there is a clopen neighborhood
on which `f` is simple.
The proof uses `exists_clopen_subset_of_open` (clopen basis) and the CB analysis.
commented this abstract version for a concrete one in the Baire space
theorem decomposition_lemma {X Y : Type*}
[TopologicalSpace X] [SeparableSpace X] [MetrizableSpace X]
[TotallyDisconnectedSpace X]
[TopologicalSpace Y]
{f : X → Y} (hf : ScatteredFun f) :
∀ x : X, ∃ U : Set X, IsClopen U ∧ x ∈ U ∧
SimpleFun (f ∘ (Subtype.val : U → X)) := by
sorry


**Decomposition Lemma (corrected).** Any scattered function `f : A → Baire`
with `A ⊆ Baire` is locally simple: around each point of `A` there is a clopen
neighborhood (in the Baire space) on which `f` is simple.
-/
theorem decomposition_lemma_baire
    (A : Set Baire)
    (f : A → Baire)
    (hf : ScatteredFun f) :
    ∀ x : A, ∃ U : Set Baire, IsClopen U ∧ (x : Baire) ∈ U ∧
         SimpleFun ((f ∘ (Subtype.val : {a : A | (a : Baire) ∈ U} → A)))
     := by
  -- proof differ from the mmemoir. It relies on the exit ordinal for each point in the domain.
  intros x
  obtain ⟨β, hβ⟩ : ∃ β : Ordinal.{0}, x ∈ CBLevel f β ∧ x ∉ CBLevel f (Order.succ β) := by
    have h_empty : CBLevel f (CBRank f) = ∅ := by
      -- Apply the lemma that states the CBLevel at the CB rank is empty.
      apply cbLevel_at_cbRank_empty; assumption;
    have h_exists_beta : ∃ β : Ordinal.{0}, x ∉ CBLevel f β := by
      exact ⟨ _, fun hx => h_empty.subset hx ⟩;
    exact exit_ordinal_is_successor x _ h_exists_beta.choose_spec |> fun ⟨ β, hβ₁, hβ₂, hβ₃ ⟩ => ⟨ β, hβ₂, hβ₃ ⟩;
  obtain ⟨U, hU_open, hxU, hU_empty, hU_const⟩ : ∃ U : Set A, IsOpen U ∧ x ∈ U ∧ CBLevel f (Order.succ β) ∩ U = ∅ ∧ ∀ y ∈ U ∩ CBLevel f β, f y = f x := by
    apply isolatedLocus_gives_simple_neighborhood;
    exact Classical.not_not.1 fun h => hβ.2 <| by rw [ CBLevel_succ' ] ; exact ⟨ hβ.1, h ⟩ ;
  obtain ⟨V, hV_clopen, hxV, hV_subset⟩ : ∃ V : Set Baire, IsClopen V ∧ x.val ∈ V ∧ Subtype.val ⁻¹' V ⊆ U := by
    obtain ⟨W, hW_open, hxW, hW_subset⟩ : ∃ W : Set Baire, IsOpen W ∧ x.val ∈ W ∧ Subtype.val ⁻¹' W ⊆ U := by
      rcases hU_open with ⟨ W, hW_open, rfl ⟩ ; use W; aesop;
    exact Exists.elim ( baire_exists_clopen_subset_of_open x.val W hW_open hxW ) fun V hV => ⟨ V, hV.1, hV.2.1, Set.Subset.trans ( Set.preimage_mono hV.2.2 ) hW_subset ⟩;
  refine' ⟨ V, hV_clopen, hxV, _ ⟩;
  apply restriction_to_clopen_is_simple f hf β V hV_clopen ⟨x, hxV, hβ.left⟩ (by
  exact Set.eq_empty_of_forall_notMem fun y hy => hU_empty.subset ⟨ hy.1, hV_subset hy.2 ⟩) (by
  exact ⟨ f x, fun z hz => hU_const z ⟨ hV_subset hz.1, hz.2 ⟩ ⟩)

end DecompositionLemma
