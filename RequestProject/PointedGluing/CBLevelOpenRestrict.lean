import RequestProject.PointedGluing.CBRankHelpers

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
## CB Level of open restrictions

For an open subset `S` of `X`, the CB levels of `f` restricted to `S` equal
the intersection of `S` with the CB levels of `f` on the ambient space.
-/

/-
For an open subset `S ⊆ X`, the isolated locus of `f|_S` on `S ∩ A` corresponds
to `S ∩ isolatedLocus f A`.
-/
lemma isolatedLocus_open_restrict {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set X) (hS : IsOpen S) (A : Set X)
    (_hSA : S ∩ CBLevel f 0 = S) -- trivially true, just for structure
    (x : S) (hxA : x.val ∈ A) :
    (x ∈ isolatedLocus (f ∘ Subtype.val : S → Y) (Subtype.val ⁻¹' A)) ↔
    (x.val ∈ isolatedLocus f A) := by
  constructor <;> intro h <;> rcases h with ⟨U, hU₁, hU₂, hU₃⟩ <;> simp_all +decide [ isolatedLocus ]
  · rcases hU₂ with ⟨U, hU₁, rfl⟩
    exact ⟨U ∩ S, hU₁.inter hS, ⟨hU₃.1, x.2⟩, fun y hy hyA => hU₃.2 y hy.2 hy.1 hyA⟩
  · exact ⟨Subtype.val ⁻¹' hU₁, hU₂.preimage continuous_subtype_val, hU₃.1, fun a ha ha' ha'' => hU₃.2 a ha' ha''⟩

/-
For an open subset `S ⊆ X`, `CBLevel (f ∘ Subtype.val : S → Y) β` equals
`Subtype.val ⁻¹' (CBLevel f β)` — i.e., a point `x : S` is in the CB level of the
restriction iff `x.val` is in the CB level of the full function.
-/
lemma CBLevel_open_restrict {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (S : Set X) (hS : IsOpen S) (β : Ordinal.{0})
    (x : S) :
    x ∈ CBLevel (f ∘ Subtype.val : S → Y) β ↔ x.val ∈ CBLevel f β := by
  have h_ind : ∀ β : Ordinal.{0}, Subtype.val ⁻¹' CBLevel f β = CBLevel (fun (z : S) => f z.val) β := by
    intro β
    induction' β using Ordinal.limitRecOn with β ih
    · simp +decide [ CBLevel ]
    · simp +decide [ CBLevel_succ', ih ]
      simp +decide [ ← ih, isolatedLocus ]
      congr! 3
      constructor <;> rintro ⟨h₁, U, hU₁, hU₂, hU₃⟩
      · exact ⟨h₁, Subtype.val ⁻¹' U, hU₁.preimage continuous_subtype_val, hU₂, fun a ha ha' ha'' => hU₃ a ha' ha''⟩
      · obtain ⟨V, hV₁, hV₂⟩ := hU₁
        refine' ⟨h₁, V ∩ S, hV₁.inter hS, _, _⟩ <;> aesop
    · simp_all +decide [ Set.ext_iff, CBLevel_limit ]
  exact Set.ext_iff.mp ( h_ind β ) x |>.symm

/-
If `f` is scattered, then `f` restricted to any subset is also scattered.
-/
lemma scattered_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) :
    ScatteredFun (f ∘ Subtype.val : S → Y) := by
  intro T hT
  obtain ⟨U, hU_open, hU_nonempty⟩ := hf (Subtype.val '' T) (by
  exact hT.image _)
  refine' ⟨Subtype.val ⁻¹' U, _, _, _⟩ <;> simp_all +decide [ Set.Nonempty ]
  · exact hU_open.preimage continuous_subtype_val
  · exact fun x hx hx' hx'' y hy hy' hy'' => hU_nonempty.2 x hx' hx hx'' y hy' hy hy''

/-
CBRank of a restriction to an open set is bounded by CBRank of the full function,
    when both are scattered.
-/
lemma CBRank_open_restrict_le {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) (hS : IsOpen S) :
    CBRank (f ∘ Subtype.val : S → Y) ≤ CBRank f := by
  refine' csInf_le _ _
  · exact ⟨0, fun α hα => zero_le α⟩
  · ext x
    rw [ CBLevel_open_restrict, CBLevel_open_restrict ]
    · have := CBLevel_eq_empty_at_rank f hf
      simp_all +decide [ CBLevel ]
    · exact hS
    · exact hS

/-
If `f` is scattered with CB rank `r`, and `S` is open, then
    `CBLevel (f|_S) r = ∅`.
-/
lemma CBLevel_open_restrict_empty_at_rank {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Small.{0} X]
    (f : X → Y) (hf : ScatteredFun f) (S : Set X) (hS : IsOpen S) :
    CBLevel (f ∘ Subtype.val : S → Y) (CBRank f) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx; have := CBLevel_eq_empty_at_rank f hf; simp_all +decide [ CBLevel_open_restrict ] 

/-
For a clopen disjoint union, the CB rank is at most the supremum.
-/
lemma CBLevel_open_union_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Small.{0} X]
    (f : X → Y)
    (S : ℕ → Set X)
    (hS_open : ∀ n, IsOpen (S n))
    (hS_cover : ∀ x : X, ∃ n, x ∈ S n)
    (β : Ordinal.{0})
    (hS_empty : ∀ n, CBLevel (f ∘ Subtype.val : S n → Y) β = ∅) :
    CBLevel f β = ∅ := by
  ext x
  obtain ⟨n, hn⟩ := hS_cover x
  specialize hS_empty n
  simp_all +decide [ CBLevel_open_restrict, Set.ext_iff ]

-- lemma CBLevel_clopen_union_empty {X Y : Type*}
--     [TopologicalSpace X] [TopologicalSpace Y]
--     {f : X → Y} {I : Type*} {A : I → Set X} {α : Ordinal.{0}}
--     (h_cover : (⋃ i, A i) = Set.univ)
--     (h_clopen : ∀ i, IsClopen (A i))
--     (h_empty : ∀ i, CBLevel (fun (x : A i) => f x.val) α = ∅) :
--     CBLevel f α = ∅ := by
--   ext x
--   simp only [Set.mem_empty_iff_false, iff_false]
--   intro hx
--   have hx_mem : x ∈ ⋃ i, A i := h_cover ▸ Set.mem_univ x
--   obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx_mem
--   have hkey := local_cb_derivative (A i) (h_clopen i).isOpen α (f := f)
--   have hx_img : x ∈ Subtype.val '' CBLevel (f ∘ (Subtype.val : A i → X)) α :=
--     (Set.ext_iff.mp hkey x).mpr (Set.mem_inter hx hi)
--   obtain ⟨xi, hxi_mem, _⟩ := hx_img
--   -- hxi_mem : xi ∈ CBLevel (f ∘ Subtype.val) α
--   -- h_empty i : CBLevel (fun x : A i => f x.val) α = ∅
--   -- (fun x : A i => f x.val) and (f ∘ Subtype.val) are definitionally equal
--   -- so we can rewrite hxi_mem using h_empty i directly
--   have : xi ∈ (∅ : Set (A i)) := h_empty i ▸ hxi_mem
--   exact this

end
