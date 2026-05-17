import RequestProject.PointedGluing.SelfSimilarity

open scoped Topology
open Set Function TopologicalSpace Classical

set_option autoImplicit false

noncomputable section

/-!
## Helper lemmas for combining clopen partition pieces
-/

/-- ContinuouslyReduces is preserved under restriction to a subtype. -/
lemma ContinuouslyReduces.restrict_subtype
    {A : Type*} [TopologicalSpace A] {Y : Type*} [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : A → Y} {g : X' → Y'} (hfg : ContinuouslyReduces f g)
    (D : Set A) :
    ContinuouslyReduces (fun x : D => f x.val) g := by
  cases hfg
  rename_i h₁ h₂
  use fun x => h₁ x
  refine ⟨h₂.1.comp continuous_subtype_val, h₂.2.choose, ?_, ?_⟩
  · refine h₂.2.choose_spec.1.mono ?_
    exact Set.range_subset_iff.2 fun x => ⟨x, rfl⟩
  · exact fun x => h₂.2.choose_spec.2 x

/-- ContinuouslyReduces from a function on D ⊆ C, given a reduction from C. -/
lemma ContinuouslyReduces.restrict_of_subset
    {A : Type*} [TopologicalSpace A] {Y : Type*} [TopologicalSpace Y]
    {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    {f : A → Y} {g : X' → Y'}
    {C D : Set A} (hDC : D ⊆ C)
    (hfg : ContinuouslyReduces (fun x : C => f x.val) g) :
    ContinuouslyReduces (fun x : D => f x.val) g := by
  obtain ⟨σ, τ, hσ, hτ, h_eq⟩ := hfg
  use fun x => σ ⟨x.val, hDC x.prop⟩
  refine ⟨?_, ?_⟩
  · fun_prop
  · refine ⟨hσ, hτ.mono ?_, ?_⟩
    · grind
    · exact fun x => h_eq ⟨x, hDC x.2⟩

set_option maxHeartbeats 4000000 in
/-- Clopen partition combining: if each piece reduces to `Subtype.val` on `B`,
    then `f` reduces to `Subtype.val` on `GluingSet(fun _ => B)`. -/
lemma clopen_partition_to_gluing_reduces
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (P : ℕ → Set A)
    (hP_clopen : ∀ i, IsClopen (P i))
    (hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hP_cover : ⋃ i, P i = Set.univ)
    {B : Set (ℕ → ℕ)}
    (hred : ∀ i, ContinuouslyReduces (fun x : P i => f x.val) (fun x : B => (x.val : ℕ → ℕ))) :
    ContinuouslyReduces f (fun x : GluingSet (fun _ => B) => (x.val : ℕ → ℕ)) := by
  choose σ hσ using hred
  choose τ hτ₁ hτ₂ using fun i => hσ i |>.2
  obtain ⟨σ', hσ'⟩ : ∃ σ' : A → ℕ → ℕ, Continuous σ' ∧ ∀ x : A, σ' x = prepend (partitionIndex P hP_cover x) (σ (partitionIndex P hP_cover x) ⟨x, partitionIndex_mem P hP_cover x⟩).val := by
    have h_cont : Continuous (fun x : A => partitionIndex P hP_cover x) := by
      convert partitionIndex_locallyConstant P hP_clopen hP_disj hP_cover using 1
      grind +suggestions
    have h_cont : ∀ i, Continuous (fun x : P i => prepend i (σ i x).val) := by
      intro i; specialize hσ i; exact (by
      exact Continuous.comp (show Continuous fun x : ℕ → ℕ => prepend i x from by exact continuous_pi fun n => by cases n <;> continuity) (show Continuous fun x : P i => (σ i x : ℕ → ℕ) from by exact Continuous.comp (show Continuous fun x : B => (x : ℕ → ℕ) from by continuity) hσ.1))
    have := continuous_pasting_on_clopen P Set.univ hP_clopen hP_disj hP_cover (fun i => fun x : P i => prepend i (σ i x).val) (fun i => h_cont i)
    simp +zetaDelta at *
    obtain ⟨h, hh₁, hh₂⟩ := this (by
      intro a ha i hi j hj; have := hP_disj i j; simp_all +decide [Set.disjoint_left]
      grind)
    exact ⟨fun x => h ⟨x, trivial⟩, hh₁.comp <| by continuity, fun a ha => hh₂ a ha _ <| partitionIndex_mem P hP_cover _⟩
  have hτ_cont : ContinuousOn (fun z => τ (z 0) (unprepend z)) (Set.range (fun x => σ' x)) := by
    apply continuousOn_piecewise_clopen
    case τ_i => exact fun i z => τ i (unprepend z)
    case S_i => exact fun i => { z : ℕ → ℕ | z 0 = i }
    all_goals norm_num [isClopen_preimage_zero]
    intro i
    refine ContinuousOn.comp (hτ₁ i) ?_ ?_
    · exact Continuous.continuousOn (by exact continuous_pi fun _ => continuous_apply _)
    · rintro _ ⟨⟨x, rfl⟩, hx⟩
      simp_all +decide [prepend]
      use x.val
      use x.2
      use by
        exact hx ▸ partitionIndex_mem P hP_cover x
      generalize_proofs at *
      unfold unprepend prepend; aesop
  have h_eq : ∀ x : A, f x = τ (σ' x 0) (unprepend (σ' x)) := by
    intro x; specialize hτ₂ (partitionIndex P hP_cover x) ⟨x, partitionIndex_mem P hP_cover x⟩ ; aesop
  use fun x => ⟨σ' x, by
    exact hσ'.2 x ▸ mem_gluingSet_prepend (σ (partitionIndex P hP_cover x) ⟨x, partitionIndex_mem P hP_cover x⟩ |>.2)⟩
  generalize_proofs at *
  exact ⟨by exact Continuous.subtype_mk hσ'.1 _, _, hτ_cont, fun x => h_eq x⟩

/-- If every point of A has a clopen neighborhood in A where f reduces to MaxFun α,
    then f globally reduces to MaxFun α. -/
lemma locally_reduces_to_maxfun_implies_reduces
    (α : Ordinal.{0}) (hα : α < omega1)
    {A : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ)
    (hloc : ∀ x : A, ∃ C : Set A, IsClopen C ∧ x ∈ C ∧
        ContinuouslyReduces (fun a : C => f a.val) (MaxFun α)) :
    ContinuouslyReduces f (MaxFun α) := by
  -- Extract clopen cover and reductions
  obtain ⟨S, hS⟩ : ∃ S : Set A, S.Countable ∧ ⋃ x ∈ S, (Classical.choose (hloc x)) = Set.univ := by
    have h_lindelof : IsLindelof (Set.univ : Set A) := by
      exact isLindelof_univ
    have := h_lindelof.elim_nhds_subcover (fun x => Classical.choose (hloc x)) fun x _ => Classical.choose_spec (hloc x) |>.1.2.mem_nhds (Classical.choose_spec (hloc x) |>.2.1) ; aesop
  have := hS.1.exists_eq_range
  by_cases hS_empty : S = ∅ <;> simp_all +decide [Set.ext_iff]
  · constructor
    swap
    exact fun x => False.elim <| hS x x.2
    exact ⟨continuous_of_const fun x y => by tauto, fun _ => 0, continuousOn_const, fun x => by tauto⟩
  · obtain ⟨g, hg⟩ := this ⟨_, hS_empty.choose_spec.choose_spec⟩
    -- Let $P_n = \text{disjointed}(C(g(n)))$.
    set P : ℕ → Set A := fun n => disjointed (fun n => Classical.choose (hloc (g n))) n
    -- Each $P_n$ is clopen and pairwise disjoint.
    have hP_clopen : ∀ n, IsClopen (P n) := by
      intro n
      apply disjointed_clopen
      exact fun n => Classical.choose_spec (hloc (g n)) |>.1
    have hP_disj : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
      exact fun i j hij => disjoint_disjointed _ hij
    have hP_cover : ⋃ i, P i = Set.univ := by
      ext x; simp [P]
      have := hS.2 x x.2
      obtain ⟨i, hi, hi', hi''⟩ := this
      obtain ⟨n, hn⟩ := hg _ hi |>.1 hi'
      have h_exists_n : ∃ n, x ∈ Classical.choose (hloc (g n)) ∧ ∀ m < n, x ∉ Classical.choose (hloc (g m)) := by
        exact ⟨Nat.find (⟨n, by aesop⟩ : ∃ n, x ∈ Classical.choose (hloc (g n))), Nat.find_spec (⟨n, by aesop⟩ : ∃ n, x ∈ Classical.choose (hloc (g n))), fun m mn => Nat.find_min (⟨n, by aesop⟩ : ∃ n, x ∈ Classical.choose (hloc (g n))) mn⟩
      obtain ⟨n, hn₁, hn₂⟩ := h_exists_n; use n; simp_all +decide [disjointed]
    -- Each $P_n$ reduces to $MaxFun \alpha$.
    have hP_reduces : ∀ n, ContinuouslyReduces (fun x : P n => f x.val) (MaxFun α) := by
      intro n
      have := Classical.choose_spec (hloc (g n))
      exact ContinuouslyReduces.restrict_of_subset (show P n ⊆ Classical.choose (hloc (g n)) from disjointed_subset _ _) this.2.2
    convert clopen_partition_to_gluing_reduces f P hP_clopen hP_disj hP_cover hP_reduces |> fun h => h.trans (gluingSet_copies_reduces_to_MaxFun α hα) using 1

/-- Homeomorphism between {a : A | a.val ∈ U} and A ∩ U -/
def subtypeInterHomeo (A U : Set (ℕ → ℕ)) :
    {a : A | (a : ℕ → ℕ) ∈ U} ≃ₜ (A ∩ U : Set (ℕ → ℕ)) where
  toFun a := ⟨a.val.val, ⟨a.val.prop, a.prop⟩⟩
  invFun x := ⟨⟨x.val, x.prop.1⟩, x.prop.2⟩
  left_inv a := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun := by
    exact continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ ?_
    exact continuous_subtype_val |>.subtype_mk _

/-- Transfer: f ∘ Subtype.val on {a ∈ A | a.val ∈ U} equals f' ∘ e. -/
lemma subtype_inter_fun_eq (A U : Set (ℕ → ℕ)) (f : A → ℕ → ℕ) :
    f ∘ (Subtype.val : {a : A | (a : ℕ → ℕ) ∈ U} → A) =
    (fun x : (A ∩ U : Set (ℕ → ℕ)) => f ⟨x.val, x.prop.1⟩) ∘ (subtypeInterHomeo A U) := by
  ext a; simp [subtypeInterHomeo]

end
