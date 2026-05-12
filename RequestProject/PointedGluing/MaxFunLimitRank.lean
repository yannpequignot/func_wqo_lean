import RequestProject.PointedGluing.GeneralStructureHelpers
import RequestProject.PrelimMemo.Scattered.CBAnalysis

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/-!
# Formalization of MaxFun_le_limit_rank

This file formalizes the "tree argument" for the limit case of the General Structure Theorem:
  MaxFun(η) ≤ g  when  η is a limit ordinal and CBRank g = η.

## Strategy

1. Define `BaNbhd s` for a finite sequence `s : Fin n → ℕ` — the basic clopen
   neighborhood `{h : ℕ → ℕ | ∀ i : Fin n, h i = s i}` (analogous to `nbhd x n`
   in the Baire space, but indexed by a finite sequence rather than an initial segment
   of a fixed point).

2. Define the **tree** `T = {s | CBRank (g corestr BaNbhd s) = η}`, which is
   non-empty (the empty sequence is in T since BaNbhd ∅ = ℕ → ℕ) and closed under
   initial segments (prefixes).

3. Let `[T]` be the **body** of T: `{x : ℕ → ℕ | ∀ n, x ↾ n ∈ T}`.
   - If `[T]` is infinite: apply `InfiniteEmbedOmega` to get pairwise incomparable
     sequences `(sₙ)` with each `BaNbhd sₙ` satisfying `CBRank (g corestr BaNbhd sₙ) = η`.
   - If `[T]` is finite: let F be the ⊏-minimal elements of `ℕ^{<ℕ} \ T`. The values
     `{CBRank (g corestr BaNbhd s) | s ∈ F}` are cofinal in η (else some β bounds all
     of them, forcing CB_β(g) ⊆ g⁻¹([T]), but [T] finite implies CB_{β+1}(g) = ∅,
     contradicting CBRank g = η > β + 1). In either case we get a sequence (sₙ) of
     pairwise incomparable finite sequences such that CBRank (g corestr BaNbhd sₙ) is
     either constantly η or cofinal in η and < η.

4. Apply the induction hypothesis and `gluing_reduces_to_pgluing_via_injection` to
   the disjoint clopen sets `(BaNbhd sₙ)ₙ`.
-/

-- ============================================================
-- §1  Basic clopen neighborhoods indexed by finite sequences
-- ============================================================

/-- `BaNbhd s` is the basic clopen neighborhood determined by the finite sequence
`s : Fin n → ℕ`: the set of all `h : ℕ → ℕ` whose first `n` values agree with `s`.
This is the analogue of `nbhd x n = {h | ∀ i < n, h i = x i}` but parametrized
by an *abstract* finite sequence rather than a point in Baire space. -/
def BaNbhd {n : ℕ} (s : Fin n → ℕ) : Set (ℕ → ℕ) :=
  {h : ℕ → ℕ | ∀ i : Fin n, h i = s i}

-- ── Basic properties of BaNbhd ──────────────────────────────

/-- `BaNbhd` of the empty sequence is the whole Baire space. -/
lemma BaNbhd_empty : BaNbhd (Fin.elim0 : Fin 0 → ℕ) = Set.univ := by
  simp [BaNbhd]

lemma BaNbhd.as_inter {n : ℕ} (s : Fin n → ℕ)
  : BaNbhd s = ⋂ i : Fin n, {h : ℕ → ℕ | h i = s i} := by
    ext h; simp [BaNbhd, Set.mem_iInter]

/-- `BaNbhd s` is open. -/
lemma BaNbhd_isOpen {n : ℕ} (s : Fin n → ℕ) : IsOpen (BaNbhd s) := by
  -- BaNbhd s = ⋂ i : Fin n, {h | h i = s i}
  -- Each {h | h i = s i} = (fun h => h i) ⁻¹' {s i} is open (discrete codomain).
  have h_open : IsOpen (⋂ i : Fin n, {h : Baire | h i = s i}) := by
    apply isOpen_iInter_of_finite
    intro i
    have h_preimage : {h : Baire | h i = s i} = (fun h => h (i : ℕ)) ⁻¹' {s i} := rfl
    rw [h_preimage]
    exact (isOpen_discrete {s i}).preimage (continuous_apply (i : ℕ))
  rw[BaNbhd.as_inter]
  exact h_open

/-- `BaNbhd s` is closed (it is also the intersection of finitely many closed sets). -/
lemma BaNbhd_isClosed {n : ℕ} (s : Fin n → ℕ) : IsClosed (BaNbhd s) := by

  have h_closed : IsClosed (⋂ i : Fin n, {h : Baire | h i = s i}) := by
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_apply (i : ℕ)) continuous_const
  rw [BaNbhd.as_inter]
  exact h_closed

/-- `BaNbhd s` is clopen. -/
lemma BaNbhd_isClopen {n : ℕ} (s : Fin n → ℕ) : IsClopen (BaNbhd s) :=
  ⟨BaNbhd_isClosed s, BaNbhd_isOpen s⟩

/-- `BaNbhd s` is nonempty: the sequence `s` extended by zeros belongs to it. -/
lemma BaNbhd_nonempty {n : ℕ} (s : Fin n → ℕ) : (BaNbhd s).Nonempty := by
  use fun k => if h : k < n then s ⟨k, h⟩ else 0
  simp [BaNbhd]

-- ── Prefix order on finite sequences ────────────────────────

/-- `s` is a prefix of `t` (or `t` extends `s`): `n ≤ m` and the first `n` values
of `t` agree with `s`. -/
def IsPrefix {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ) : Prop :=
  ∃ h : n ≤ m, ∀ i : Fin n, s i = t ⟨i, i.isLt.trans_le h⟩

/-- If `s` is a prefix of `t` then `BaNbhd t ⊆ BaNbhd s`. -/
lemma BaNbhd_antitone {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hpre : IsPrefix s t) : BaNbhd t ⊆ BaNbhd s := by
  intro h hh
  simp only [BaNbhd, Set.mem_setOf_eq] at *
  intro i
  rw [hpre.2 i, ← hh ⟨i, i.isLt.trans_le hpre.1⟩]

-- ── Extension of finite sequences ────────────────────────────

/-- Extend a finite sequence `s : Fin n → ℕ` by appending the value `k`. -/
def extendSeq {n : ℕ} (s : Fin n → ℕ) (k : ℕ) : Fin (n + 1) → ℕ :=
  Fin.snoc s k
/-- The extension `extendSeq s k` extends `s`. -/
lemma extendSeq_isPrefix {n : ℕ} (s : Fin n → ℕ) (k : ℕ) :
    IsPrefix s (extendSeq s k) :=
  ⟨Nat.le_succ n, fun i => by
    simp only [extendSeq, Fin.snoc]
    split_ifs with h
    · congr 1;
    · exact absurd i.isLt (by omega)⟩

/-- `BaNbhd`s for different extensions are pairwise disjoint. -/
lemma BaNbhd_extend_disjoint {n : ℕ} (s : Fin n → ℕ) (j k : ℕ) (hjk : j ≠ k) :
    Disjoint (BaNbhd (extendSeq s j)) (BaNbhd (extendSeq s k)) := by
  simp only [Set.disjoint_left, BaNbhd, Set.mem_setOf_eq, extendSeq]
  intro h hj hk
  have hj' : h n = j := by
    have := hj ⟨n, Nat.lt_succ_self n⟩
    simp [Fin.snoc, Fin.last] at this
    exact this
  have hk' : h n = k := by
    have := hk ⟨n, Nat.lt_succ_self n⟩
    simp [Fin.snoc, Fin.last] at this
    exact this
  exact hjk (by omega)

-- ============================================================
-- §2  The tree T and its body [T]
-- ============================================================

section TreeArgument

variable {B : Set (ℕ → ℕ)} {g : B → ℕ → ℕ}
variable (η : Ordinal.{0})

/-- The restriction of `g` to the preimage of a set `S ⊆ ℕ → ℕ`. -/
def gRestr (S : Set (ℕ → ℕ)) : {x : B | g x ∈ S} → ℕ → ℕ :=
  fun x => g x.val

/-- The CB rank of `g` restricted to the preimage of `BaNbhd s`. -/
noncomputable def cbRankRestr (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) {n : ℕ} (s : Fin n → ℕ) : Ordinal.{0} :=
  CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val)

/-- The tree: all finite sequences whose associated CB-rank restriction equals η. -/
def TreeT (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (η : Ordinal.{0}) :
    (Σ n : ℕ, Fin n → ℕ) → Prop :=
  fun ⟨_, s⟩ => cbRankRestr B g s = η


lemma CoRestr_BaNbhd_empty : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} = Set.univ := by
  simp [BaNbhd_empty]

/-- The empty sequence is in T: BaNbhd ∅ = univ, so gRestr univ = g, and CBRank g = η. -/
lemma TreeT_contains_empty (hg : ScatteredFun g) (hrank : CBRank g = η) :
    TreeT B g η ⟨0, Fin.elim0⟩ := by
  unfold TreeT cbRankRestr
  have hmem : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} = Set.univ :=
    CoRestr_BaNbhd_empty
  have hopen : IsOpen ({b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} : Set B) :=
    hmem ▸ isOpen_univ
  have hle : CBRank (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
      g x.val) ≤ CBRank g :=
    CBRank_open_restrict_le g hg _ hopen
  have hred : ContinuouslyReduces g (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
    g x.val) := by
    refine ⟨fun b => ⟨b, hmem ▸ Set.mem_univ b⟩, Continuous.subtype_mk continuous_id _,
          id, continuousOn_id, fun b => rfl⟩
  have hge : CBRank g ≤ CBRank (fun x : {b : B | g b ∈ BaNbhd (Fin.elim0 : Fin 0 → ℕ)} =>
    g x.val) :=
    ContinuouslyReduces.rank_monotone hg (scattered_restrict g hg _) hred
  simp only []
  exact (le_antisymm hle hge).trans hrank


/-- T is closed under prefixes: if t ∈ T and s is a prefix of t, then s ∈ T. -/
lemma TreeT_prefix_closed {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hpre : IsPrefix s t) (ht : TreeT B g η ⟨m, t⟩)
    (hg : ScatteredFun g) (hgc : Continuous g) :
    TreeT B g η ⟨n, s⟩ := by
  simp only [TreeT, cbRankRestr] at *
  -- BaNbhd t ⊆ BaNbhd s, so preimage of BaNbhd t ⊆ preimage of BaNbhd s
  -- CBRank (g restr BaNbhd t) = η implies CBRank (g restr BaNbhd s) = η
  -- because BaNbhd t ⊆ BaNbhd s gives a "sub-restriction"
  -- and CBRank is monotone under open supersets when g is scattered.
  -- KEY: CB_η(gRestr (BaNbhd t)) = ∅ and CB_η(gRestr (BaNbhd s)) maps
  -- We use cb_rank_of_clopen_union: if BaNbhd s = BaNbhd t ∪ (rest) and
  -- CBRank on BaNbhd t = η, then CBRank on BaNbhd s ≥ η.
  -- Also CBRank on BaNbhd s ≤ η = CBRank g (monotonicity of restriction).
  sorry

/-- The body of T: sequences x : ℕ → ℕ such that every finite initial segment of x is in T. -/
def BodyT : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∀ n : ℕ, TreeT B g η ⟨n, fun i => x i⟩}

end TreeArgument

-- ============================================================
-- §3  Main lemma
-- ============================================================

/-- **Tree argument.** For a limit ordinal η with CBRank g = η,
MaxFun(η) continuously reduces to g.

**Proof sketch:**
1. Build the tree `T = {s ∈ ℕ^{<ℕ} | CBRank(g corestr BaNbhd s) = η}`.
   - T is nonempty (empty sequence is in T since BaNbhd ∅ = Baire and CBRank g = η).
   - T is closed under prefixes (CBRank is monotone: going to a larger BaNbhd
     can only increase the CB rank, so if the smaller set already has rank η,
     the larger does too).

2. Let [T] = body of T = {x | ∀ n, x ↾ n ∈ T}.

3. **Case A: [T] is infinite.**
   Apply `InfiniteEmbedOmega` to find an injection ℕ → [T] → T giving a sequence
   (sₙ)ₙ of pairwise ⊏-incomparable elements with CBRank(g corestr BaNbhd sₙ) = η
   for all n. The BaNbhd sₙ are pairwise disjoint clopen sets.
   By the induction hypothesis (on ordinals < η for the IH in MaxFun_le_MinFun),
   MaxFun(η) ≤ each g corestr BaNbhd sₙ.
   Apply `gluing_reduces_to_pgluing_via_injection` to conclude.

4. **Case B: [T] is finite.**
   Let F = ⊏-minimal elements of ℕ^{<ℕ} \ T.
   Since [T] is finite and T is a subtree of ℕ^{<ℕ}, F is finite and nonempty.
   Claim: {CBRank(g corestr BaNbhd s) | s ∈ F} is cofinal in η.
   *Proof of claim (by contradiction):* If some β < η bounds all these ranks,
   then CB_β(g) ∩ g⁻¹(BaNbhd s) = ∅ for all s ∈ F (since CBRank < β means
   CB_β level is empty). But the BaNbhd s for s ∈ F cover the complement of [T],
   so CB_β(g) ⊆ g⁻¹([T]). Since [T] is finite, every point in g⁻¹([T]) is
   isolated in CB_β(g), giving CB_{β+1}(g) = ∅, so CBRank g ≤ β + 1 < η. Contradiction.
   Hence we can extract a sequence (sₙ)ₙ with s ∈ F and CBRank(g corestr BaNbhd sₙ)
   cofinal in η, still pairwise incomparable (elements of F are ⊏-antichains).
   Apply the IH and `gluing_reduces_to_pgluing_via_injection`. -/
private lemma MaxFun_le_limit_rank (η : Ordinal.{0}) (hη : η < omega1)
    (hlam : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g) (hg : ScatteredFun g)
    (hrank : CBRank g = η) :
    ContinuouslyReduces (MaxFun η) g := by
  -- Step 1: Build tree T and note it is nonempty and prefix-closed.
  -- T_prop n s : Prop := CBRank (gRestr (BaNbhd s)) = η
  let T_prop : ∀ n : ℕ, (Fin n → ℕ) → Prop :=
    fun _ s => CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) = η
  -- The empty sequence is in T.
  have hT_nonempty : T_prop 0 Fin.elim0 := by
    simp only [T_prop]
    convert hrank using 2; simp
    sorry
  -- Step 2: Define the body [T].
  let bodyT : Set (ℕ → ℕ) :=
    {x : ℕ → ℕ | ∀ n, T_prop n (fun i => x i)}
  -- Step 3: Case split on whether bodyT is infinite or finite.
  by_cases hbody : Set.Infinite bodyT
  · -- ── Case A: [T] is infinite ──────────────────────────────
    -- There exist pairwise incomparable (sₙ) in T with CBRank(g|BaNbhd sₙ) = η.
    -- (In the infinite body case we can pick leaves: for each x ∈ bodyT and each n,
    --  x ↾ n is a distinct element of T; since bodyT is infinite and T is a tree,
    --  T itself is infinite, and by König's lemma / InfiniteEmbedOmega we find
    --  a sequence of pairwise incomparable elements.)
    -- For the formalization skeleton we record the key steps as sorries.
    -- Obtain sequence of pairwise incomparable sₙ with T_prop applied to each:
    obtain ⟨seq, hseq_incompat, hseq_T⟩ :
        ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
          (∀ i j, i ≠ j → ¬ IsPrefix (seq i).2 (seq j).2 ∧
                           ¬ IsPrefix (seq j).2 (seq i).2) ∧
          ∀ i, T_prop (seq i).1 (seq i).2 := by
      -- Apply InfiniteEmbedOmega or a direct construction from bodyT infinite.
      sorry
    -- The sets BaNbhd (seq i).2 are pairwise disjoint clopen sets.
    have hDisj : ∀ i j, i ≠ j → Disjoint (BaNbhd (seq i).2) (BaNbhd (seq j).2) := by
      intro i j hij
      -- Incomparable sequences give disjoint BaNbhd's.
      sorry
    -- For each i, MaxFun(η) ≤ g corestr BaNbhd (seq i).2:
    -- CBRank(g|BaNbhd sᵢ) = η, so by the IH MaxFun(η) ≤ g|BaNbhd sᵢ.
    -- (This is precisely `MaxFun_le_limit_rank` applied to the restriction,
    --  or alternatively `maxFun_is_maximum'` + the rank equality.)
    have hred : ∀ i, ContinuouslyReduces (MaxFun η)
        (fun x : {b : B | g b ∈ BaNbhd (seq i).2} => g x.val) := by
      intro i
      -- By the induction hypothesis on CBRank: CBRank(g|BaNbhd sᵢ) = η.
      -- Since g is scattered continuous and the restriction has the same rank η,
      -- and we need MaxFun η ≤ restriction.
      -- This follows from maxFun_is_maximum' applied to the restriction, but
      -- the IH argument here is that we will apply the overall theorem inductively;
      -- in the tree argument these are used via the gluing lemma.
      -- For now this is the key inductive step (admitted as sorry for the skeleton).
      sorry
    -- Apply gluing to conclude MaxFun η ≤ g.
    sorry
  · -- ── Case B: [T] is finite ────────────────────────────────
    -- Let F = ⊏-minimal elements of ℕ^{<ℕ} \ T.
    -- F is a finite antichain.
    -- {CBRank(g|BaNbhd s) | s ∈ F} is cofinal in η.
    -- Extract subsequence cofinal in η and apply IH + gluing.
    -- Step B1: Every x ∈ ℕ → ℕ \ bodyT has some finite initial segment not in T.
    have hBodyT_cover : ∀ x : ℕ → ℕ, x ∉ bodyT →
        ∃ n : ℕ, ¬ T_prop n (fun i => x i) := by
      intro x hx
      simp only [bodyT, Set.mem_setOf_eq, not_forall] at hx
      exact hx
    -- Step B2: The BaNbhd of minimal-not-in-T sequences cover the complement of bodyT.
    -- Step B3: Cofinality — for any β < η, ∃ s ∈ F with CBRank(g|BaNbhd s) ≥ β.
    have hCofinal : ∀ β : Ordinal.{0}, β < η →
        ∃ (n : ℕ) (s : Fin n → ℕ), ¬ T_prop n s ∧
          β < CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) := by
      intro β hβ
      -- By contradiction: if all minimal non-T sequences have CB-rank ≤ β,
      -- then CB_β(g) ⊆ g⁻¹(bodyT), but bodyT finite implies CB_{β+1}(g) = ∅,
      -- so CBRank g ≤ β + 1 < η — contradicting hrank.
      sorry
    -- Step B4: From cofinality, extract a sequence (sₙ)ₙ with
    --   CBRank(g|BaNbhd sₙ) cofinal in η, pairwise incomparable.
    obtain ⟨seq, hseq_incompat, hseq_cofinal⟩ :
        ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
          (∀ i j, i ≠ j → ¬ IsPrefix (seq i).2 (seq j).2 ∧
                           ¬ IsPrefix (seq j).2 (seq i).2) ∧
          ∀ i, cofinalSeq η i ≤
               CBRank (fun x : {b : B | g b ∈ BaNbhd (seq i).2} => g x.val) := by
      sorry
    -- Step B5: Apply IH and gluing (same structure as Case A).
    sorry
