import RequestProject.PointedGluing.CBLevelOpenRestrict

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
## Helper lemmas for CBrank_regular_simple (Proposition 3.8)
-/

/-
RaySet conditions define an open set in the Baire space.
-/
lemma RaySet_cond_isOpen (y : ℕ → ℕ) (n : ℕ) :
    IsOpen {x : ℕ → ℕ | (∀ k, k < n → x k = y k) ∧ x n ≠ y n} := by
  refine' isOpen_iff_forall_mem_open.mpr _
  intro x hx
  refine' ⟨{ z : ℕ → ℕ | ∀ k ≤ n, z k = x k }, _, _, _⟩
  · grind
  · rw [ isOpen_pi_iff ]
    intro f hf; use Finset.Iic n; use fun k => { z | z = x k } ; aesop
  · exact fun k hk => rfl


/-
The ray subtype `{a : A | f a ∈ RaySet B y n}` is open in `A` (for continuous `f`).
-/
lemma ray_subtype_isOpen (A: Set (ℕ → ℕ)) (B : Set (ℕ → ℕ))
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (y : ℕ → ℕ) (n : ℕ) :
    IsOpen ({a : A | f a ∈ RaySet B y n} : Set A) := by
  unfold RaySet
  convert RaySet_cond_isOpen y n |> IsOpen.preimage hf using 1
  aesop

lemma RaySet_subtype_eq_preimage (A : Set (ℕ → ℕ)) (y : ℕ → ℕ) (n : ℕ) :
    (Subtype.val ⁻¹' RaySet Set.univ y n : Set A) =
    Subtype.val ⁻¹' RaySet A y n := by
  ext ⟨x, hx⟩
  simp [RaySet]

lemma ray_subtype_isOpen' (A : Set (ℕ → ℕ)) (y : ℕ → ℕ) (n : ℕ) :
    IsOpen (Subtype.val ⁻¹' RaySet A y n : Set A) := by
  -- Apply ray_subtype_isOpen to the inclusion map Subtype.val : A → ℕ → ℕ
  have := ray_subtype_isOpen
    A
    Set.univ
    (Subtype.val)
    (fun a => Set.mem_univ a.val)
    (continuous_subtype_val)
    y n
  -- `this` says IsOpen {a : A | a.val ∈ RaySet A y n}
  -- which is definitionally Subtype.val ⁻¹' RaySet A y n
  rw [← RaySet_subtype_eq_preimage]
  exact this

  -- apply RaySet_subtype_eq_preimage Set.univ y n
/-
Every element of B either equals y or belongs to some RaySet.
-/
lemma mem_ray_or_eq_y {B : Set (ℕ → ℕ)} {y x : ℕ → ℕ}
    (hx : x ∈ B):
    x = y ∨ ∃ n, x ∈ RaySet B y n := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · obtain ⟨n, hn⟩ : ∃ n, (∀ k < n, x k = y k) ∧ x n ≠ y n := by
      exact ⟨Nat.find ( Function.ne_iff.mp hxy ), fun k hk => Classical.not_not.1 fun h => Nat.find_min ( Function.ne_iff.mp hxy ) hk h, Nat.find_spec ( Function.ne_iff.mp hxy )⟩
    exact Or.inr ⟨n, ⟨hx, hn⟩⟩

/-
If `CBLevel f α = ∅`, then `CBRank f ≤ α`.
-/
lemma CBRank_le_of_CBLevel_empty {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (α : Ordinal.{0})
    (h : CBLevel f α = ∅) :
    CBRank f ≤ α := by
  refine' csInf_le' _
  simp +decide [ h, CBLevel_succ' ]

/-
CBLevel of the ray function at level α is empty: by simplicity, any point in
CBLevel f α maps to y, but ray points satisfy f(x) n ≠ y n.
-/
lemma ray_CBLevel_alpha_empty {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (_hf : Continuous f)
    (α : Ordinal.{0})
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y) (n : ℕ) :
    CBLevel (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) α = ∅ := by
  contrapose! hy_simple; simp_all +decide [ CBLevel ] 
  obtain ⟨x, hx⟩ := hy_simple
  refine' ⟨x.1, x.1.2, _, _⟩
  · induction' α using Ordinal.limitRecOn with α ih generalizing x <;> simp_all +decide [ Ordinal.limitRecOn ]
    · exact ⟨ih _ x.1.2 x.2 hx.1, fun h => hx.2 <| by
        obtain ⟨U, hU₁, hU₂, hU₃⟩ := h
        refine' ⟨_, _, _⟩
        exact hx.1
        exact { y : { x : A // f x ∈ RaySet B y n } | y.val ∈ hU₁ }
        exact ⟨hU₂.preimage continuous_subtype_val, hU₃.1, fun y hy => hU₃.2 _ <| by aesop⟩⟩
    · grind
  · exact fun h => x.2.2.2 <| by simp [ h ]

/-
Each ray CB rank is ≤ α.
-/
lemma ray_cb_le_alpha {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hf : Continuous f)
    (α : Ordinal.{0})
    (y : ℕ → ℕ) (hy_simple : ∀ x ∈ CBLevel f α, f x = y) (n : ℕ) :
    CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ α := by
  exact CBRank_le_of_CBLevel_empty _ _ (ray_CBLevel_alpha_empty f hf α y hy_simple n)

/-
If for all n, the ray has CB rank ≤ β, then all points in CBLevel f β map to y.
-/
lemma CBLevel_all_rays_le_implies_const {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (y : ℕ → ℕ)
    (β : Ordinal.{0})
    (hray_le : ∀ n, CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β) :
    ∀ x ∈ CBLevel f β, f x = y := by
  intro x hx
  have h_ray_empty : ∀ n, CBLevel (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) β = ∅ := by
    intro n
    have h_ray_rank : CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β := by
      exact hray_le n
    have h_ray_empty : CBLevel (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) (CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val)) = ∅ := by
      apply CBLevel_eq_empty_at_rank
      exact scattered_restrict f hf_scat _
    exact Set.eq_empty_of_forall_notMem fun x hx => by have := CBLevel_antitone ( fun x : { a : A | f a ∈ RaySet B y n } => f x.val ) h_ray_rank hx; aesop
  contrapose! h_ray_empty
  obtain ⟨n, hn⟩ := mem_ray_or_eq_y ( hfB x ) |> Or.resolve_left <| h_ray_empty
  exact ⟨n, ⟨⟨x, hn⟩, CBLevel_open_restrict f _ ( ray_subtype_isOpen A B f hfB hf y n ) _ _ |>.2 hx⟩⟩

/-
If f is constant on CBLevel f β, then CBLevel f (succ β) = ∅.
-/
lemma CBLevel_const_succ_empty {X Y : Type*} [TopologicalSpace X]
    (f : X → Y) (β : Ordinal.{0})
    (hconst : ∀ x ∈ CBLevel f β, ∀ x' ∈ CBLevel f β, f x = f x') :
    CBLevel f (Order.succ β) = ∅ := by
  -- Since f is constant on CBLevel f β, any x in CBLevel f β is in isolatedLocus f (CBLevel f β).
  have h_isolated : ∀ x ∈ CBLevel f β, x ∈ isolatedLocus f (CBLevel f β) := by
    exact fun x hx => ⟨hx, Set.univ, isOpen_univ, trivial, fun y hy => hconst y hy.2 x hx⟩
  rw [ CBLevel_succ' ]
  exact Set.diff_eq_empty.mpr h_isolated

/-
The supremum of ray CB ranks equals α.
-/
lemma sup_ray_cb_eq_alpha {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (α : Ordinal.{0})
    (hcb_ne : (CBLevel f α).Nonempty)
    (y : ℕ → ℕ)
    (_hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (ray_cb : ℕ → Ordinal.{0})
    (hray_cb : ∀ n, ray_cb n = CBRank
      (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val))
    (hray_le : ∀ n, ray_cb n ≤ α) :
    ⨆ n, ray_cb n = α := by
  contrapose! hcb_ne
  obtain ⟨β, hβ⟩ : ∃ β : Ordinal.{0}, β < α ∧ ∀ n, ray_cb n ≤ β := by
    exact ⟨⨆ n, ray_cb n, lt_of_le_of_ne ( ciSup_le hray_le ) hcb_ne, fun n => le_ciSup ( Ordinal.bddAbove_range ray_cb ) n⟩
  have h_const : ∀ x ∈ CBLevel f β, f x = y := by
    apply CBLevel_all_rays_le_implies_const f hfB hf hf_scat y β
    aesop
  have h_empty : CBLevel f (Order.succ β) = ∅ := by
    apply CBLevel_const_succ_empty
    exact fun x hx x' hx' => h_const x hx ▸ h_const x' hx' ▸ rfl
  exact Set.eq_empty_of_forall_notMem fun x hx => by have := CBLevel_antitone f ( show α ≥ Order.succ β from Order.succ_le_of_lt hβ.1 ) hx; aesop

/-
Contrapositive regularity lemma: if ∃ β < α and m such that ∀ n > m, ray_cb n ≤ β,
    then CBLevel f α = ∅ (contradiction with hcb_ne).
-/
lemma regularity_contradiction {A B : Set (ℕ → ℕ)}
    (f : A → ℕ → ℕ) (hfB : ∀ a, f a ∈ B) (hf : Continuous f)
    (hf_scat : ScatteredFun f)
    (α : Ordinal.{0})
    (y : ℕ → ℕ) (_hy : y ∈ B)
    (hy_simple : ∀ x ∈ CBLevel f α, f x = y)
    (m : ℕ) (β : Ordinal.{0}) (hβα : β < α)
    (hbound : ∀ n, n > m → CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ β)
    (_hle : ∀ n, CBRank (fun (x : {a : A | f a ∈ RaySet B y n}) => f x.val) ≤ α) :
    CBLevel f α = ∅ := by
  -- Let $T = \{a \in A \mid \forall k \leq m, f(a)(k) = y(k)\}$.
  set T := {a : A | ∀ k ≤ m, f a k = y k}
  -- T is open in A.
  have hT_open : IsOpen T := by
    -- T is the intersection of open sets, hence it is open.
    have hT_open : IsOpen (⋂ k ∈ Finset.range (m + 1), {a : A | f a k = y k}) := by
      refine' isOpen_biInter_finset fun k hk => _
      convert ( isOpen_discrete { y k } ) |> IsOpen.preimage ( show Continuous fun a : A => f a k from ?_ ) using 1
      exact continuous_apply k |> Continuous.comp <| hf
    convert hT_open using 1
    ext; simp [T, Finset.mem_range, Nat.lt_succ_iff]
  -- For any $x \in CBLevel(f|_T) \beta$, we have $f(x.val) = y$.
  have hT_const : ∀ x : T, x.val ∈ CBLevel f β → f x.val = y := by
    intro x hx
    by_cases h : ∃ n, f x.val ∈ RaySet B y n
    · obtain ⟨n, hn⟩ := h
      by_cases hn' : n ≤ m
      · exact absurd ( x.2 n hn' ) ( by have := hn.2; aesop )
      · have h_ray_empty : CBLevel (fun x : {a : A | f a ∈ RaySet B y n} => f x.val) β = ∅ := by
          exact CBLevel_eq_empty_at_rank _ ( scattered_restrict _ hf_scat _ ) |> fun h => h ▸ Set.Subset.antisymm ( fun x hx => by
            exact CBLevel_antitone _ ( hbound n ( not_le.mp hn' ) ) hx ) ( fun x hx => by
            grind )
        have h_ray_empty : x.val ∈ CBLevel f β → x.val ∈ {a : A | f a ∈ RaySet B y n} → False := by
          intro hx hn
          have h_ray_empty : x.val ∈ CBLevel f β → x.val ∈ {a : A | f a ∈ RaySet B y n} → False := by
            intro hx hn
            have h_ray_empty : x.val ∈ CBLevel f β → x.val ∈ {a : A | f a ∈ RaySet B y n} → False := by
              have h_ray_empty : CBLevel (fun x : {a : A | f a ∈ RaySet B y n} => f x.val) β = ∅ := h_ray_empty
              intro hx hn
              apply CBLevel_open_restrict (fun x => f x) {a : A | f a ∈ RaySet B y n} (ray_subtype_isOpen A B f hfB hf y n) β ⟨x.val, hn⟩ |>.not.mp
              · exact fun h => h_ray_empty.subset h
              · exact hx
            exact h_ray_empty hx hn
          exact h_ray_empty hx hn
        exact False.elim <| h_ray_empty hx hn
    · exact Or.resolve_right ( mem_ray_or_eq_y ( hfB x ) ) h
  -- Therefore, $CBLevel(f|_T) (succ β) = ∅$.
  have hT_succ_empty : CBLevel (fun x : T => f x.val) (Order.succ β) = ∅ := by
    apply CBLevel_const_succ_empty
    intro x hx x' hx'
    rw [ hT_const x ( by
      convert CBLevel_open_restrict _ _ hT_open β x |>.1 hx using 1 ), hT_const x' ( by
      convert CBLevel_open_restrict f T hT_open β x' |>.1 hx' using 1 ) ]
  -- Since $succ β ≤ α$, we have $CBLevel(f|_T) α = ∅$.
  have hT_alpha_empty : CBLevel (fun x : T => f x.val) α = ∅ := by
    exact Set.eq_empty_of_forall_notMem fun x hx => by have := CBLevel_antitone ( fun x : T => f x.val ) ( show Order.succ β ≤ α from Order.succ_le_of_lt hβα ) ; aesop
  -- By CBLevel_open_restrict, T ∩ CBLevel f α = ∅.
  have hT_inter_empty : T ∩ CBLevel f α = ∅ := by
    have hT_inter_empty : ∀ x : T, x.val ∈ CBLevel f α → x ∈ CBLevel (fun x : T => f x.val) α := by
      intros x hx; exact (by
      convert CBLevel_open_restrict _ _ hT_open _ _ |>.2 hx using 1)
    exact Set.eq_empty_of_forall_notMem fun x hx => hT_alpha_empty.subset ( hT_inter_empty ⟨x, hx.1⟩ hx.2 )
  grind

end
