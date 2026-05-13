import Mathlib
import RequestProject.PointedGluing.GeneralStructureHelpers
import RequestProject.BaireSpace.Basics

open scoped Topology
open Set Function TopologicalSpace Classical

set_option maxHeartbeats 8000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

def gClopenDom (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) : Set (ℕ → ℕ) :=
  {x : ℕ → ℕ | ∃ (h : x ∈ B), g ⟨x, h⟩ ∈ C}

def gClopenFun (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ)) :
    gClopenDom B g C → ℕ → ℕ :=
  fun ⟨x, hx⟩ => g ⟨x, hx.choose⟩

lemma gClopenFun_continuous (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hgc : Continuous g) (C : Set (ℕ → ℕ)) :
    Continuous (gClopenFun B g C) :=
  hgc.comp (Continuous.subtype_mk continuous_subtype_val _)

lemma gClopenFun_scattered (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ)
    (hg : ScatteredFun g) (C : Set (ℕ → ℕ)) :
    ScatteredFun (gClopenFun B g C) := by
  have : ContinuouslyReduces (gClopenFun B g C) g :=
    ⟨fun x => ⟨x.val, x.prop.choose⟩,
     Continuous.subtype_mk continuous_subtype_val _,
     id, continuousOn_id, fun x => rfl⟩
  exact this.scattered hg


private lemma extract_B_map
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (C : Set (ℕ → ℕ))
    {A : Set (ℕ → ℕ)}
    (hred : ContinuouslyReduces (Subtype.val : A → ℕ → ℕ) (gClopenFun B g C)) :
    ∃ (σ : A → B) (τ : (ℕ → ℕ) → (ℕ → ℕ)),
      Continuous σ ∧
      ContinuousOn τ (Set.range (g ∘ σ)) ∧
      (∀ x, g (σ x) ∈ C) ∧
      (∀ x : A, x.val = τ (g (σ x))) := by
  obtain ⟨σ₀, hσ₀_cont, τ₀, hτ₀_cont, hτ₀_eq⟩ := hred
  refine ⟨fun x => ⟨(σ₀ x).val, (σ₀ x).prop.choose⟩, τ₀, ?_, ?_, ?_, ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp hσ₀_cont) _
  · convert hτ₀_cont using 1
  · exact fun x => (σ₀ x).prop.choose_spec
  · exact hτ₀_eq

lemma gluing_via_codomain_partition
    (η : Ordinal.{0}) (hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g)
    (C : ℕ → Set (ℕ → ℕ))
    (hC_clopen : ∀ n, IsClopen (C n))
    (hC_disj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (p : ℕ → ℕ) (hp : Function.Injective p)
    (hred : ∀ n, ContinuouslyReduces
        (Subtype.val : MaxDom (enumBelow η n) → ℕ → ℕ)
        (gClopenFun B g (C (p n)))) :
    ContinuouslyReduces (MaxFun η) g := by
  sorry

end

section TreeArgument


-- ============================================================
-- §2  The tree T and its body [T]
-- ============================================================


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
lemma TreeT_prefix_closed (heta: η = CBRank g) {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hpre : IsPrefix s t) (ht : TreeT B g η ⟨m, t⟩)
    (hg : ScatteredFun g) (hgc : Continuous g) :
    TreeT B g η ⟨n, s⟩ := by
  simp only [TreeT, cbRankRestr] at *
  -- Let Vs := {b : B | g b ∈ BaNbhd s} and Vt := {b : B | g b ∈ BaNbhd t}.
  -- BaNbhd t ⊆ BaNbhd s, so Vt ⊆ Vs.
  set Vs : Set B := {b : B | g b ∈ BaNbhd s} with hVs_def
  set Vt : Set B := {b : B | g b ∈ BaNbhd t} with hVt_def
  -- Vt ⊆ Vs  (from BaNbhd_antitone)
  have hVtVs : Vt ⊆ Vs := by
    intro b hb
    simp only [hVt_def, hVs_def, Set.mem_setOf_eq] at *
    exact BaNbhd_antitone s t hpre hb
  -- Vs is open: preimage of BaNbhd s (which is open) under the continuous map g.
  have hVs_open : IsOpen Vs := by
    have : Vs = g ⁻¹' BaNbhd s := rfl
    rw [this]
    exact (BaNbhd_isOpen s).preimage hgc
  -- Vt is open (similarly).
  have hVt_open : IsOpen Vt := by
    have : Vt = g ⁻¹' BaNbhd t := rfl
    rw [this]
    exact (BaNbhd_isOpen t).preimage hgc
  -- The restriction g|Vs is scattered (restriction of a scattered function).
  have hgs_scat : ScatteredFun (fun x : Vs => g x.val) :=
    scattered_restrict g hg Vs
  -- The restriction g|Vt is scattered.
  have hgt_scat : ScatteredFun (fun x : Vt => g x.val) :=
    scattered_restrict g hg Vt
  -- ── Upper bound: CBRank (g|Vs) ≤ CBRank (g|Vt) via open restriction ──
  -- Vt is an open subset of Vs (since Vt ⊆ Vs and Vt is open in B,
  -- so it is open in the subspace Vs).
  -- We use CBRank_open_restrict_le applied to g|Vs and the open set Vt ∩ Vs = Vt.
  -- g|Vs restricted to Vt equals g|Vt.
  have hVt_open_in_Vs : IsOpen (Subtype.val ⁻¹' Vt : Set Vs) := by
    exact hVt_open.preimage continuous_subtype_val
  -- CBRank (g|Vt) ≤ CBRank (g|Vs)  [Vt is an open subset of Vs]
  have hred : ContinuouslyReduces (fun x : Vt => g x.val) (fun x : Vs => g x.val) :=
    ⟨fun x => ⟨x.val, hVtVs x.prop⟩,
    continuous_subtype_val.subtype_mk _,
    id, continuousOn_id,
    fun _ => rfl⟩
  have hle : CBRank (fun x : Vt => g x.val)  ≤ CBRank (fun x : Vs => g x.val) :=
    ContinuouslyReduces.rank_monotone hgt_scat hgs_scat hred  -- Conclude CBRank (g|Vs) = CBRank (g|Vt) = η.
  have hge : CBRank (fun x : Vs => g x.val) ≤ CBRank (fun x : Vt => g x.val) := by
    calc CBRank (fun x : Vs => g x.val)
        ≤ CBRank g := CBRank_open_restrict_le g hg Vs hVs_open
      _ = η        := heta.symm
      _ = CBRank (fun x : Vt => g x.val) := ht.symm
  exact le_antisymm hge hle |>.trans ht


/-- If s and t are incomparable (neither is a prefix of the other),
    their BaNbhds are disjoint. -/
lemma BaNbhd_incomparable_disjoint {n m : ℕ} (s : Fin n → ℕ) (t : Fin m → ℕ)
    (hst : ¬IsPrefix s t) (hts : ¬IsPrefix t s) :
    Disjoint (BaNbhd s) (BaNbhd t) := by
  simp only [IsPrefix] at hst hts
  push_neg at hst hts
  simp only [Set.disjoint_left, BaNbhd, Set.mem_setOf_eq]
  intro h hs ht
  rcases Nat.lt_or_ge n m with hnm | hnm
  · obtain ⟨i, hi⟩ := hst hnm.le
    exact hi ((hs i).symm.trans (ht ⟨i, i.isLt.trans_le hnm.le⟩))
  · obtain ⟨i, hi⟩ := hts hnm
    exact hi ((ht i).symm.trans (hs ⟨i, i.isLt.trans_le hnm⟩))

lemma gClopenFun_CBRank_eq : ∀ (C : Set (ℕ → ℕ)), IsClopen C →
    CBRank (gClopenFun B g C) = CBRank (fun x : {b : B | g b ∈ C} => g x.val) := by
    sorry

lemma exists_disjoint_clopen_with_cofinal_ranks
    (η : Ordinal.{0}) (hη : η < omega1) (hlim : Order.IsSuccLimit η)
    (B : Set (ℕ → ℕ)) (g : B → ℕ → ℕ) (hgc : Continuous g) (hg : ScatteredFun g)
    (hrank : CBRank g = η)
    (δ : ℕ → Ordinal.{0}) (hδ : ∀ n, δ n < η) :
    ∃ (C : ℕ → Set (ℕ → ℕ)) (p : ℕ → ℕ),
      Function.Injective p ∧
      (∀ n, IsClopen (C n)) ∧
      (∀ i j, i ≠ j → Disjoint (C i) (C j)) ∧
      ∀ n, δ n < CBRank (gClopenFun B g (C (p n))) := by
  -- ── Step 1: Build the tree T ────────────────────────────────────────────
  -- T_prop n s ↔ CBRank(g|BaNbhd s) = η
  let T_prop : ∀ n : ℕ, (Fin n → ℕ) → Prop :=
    fun _ s => CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) = η
  -- The body [T] = {x : ℕ → ℕ | ∀ n, T_prop n (x ↾ n)}
  set bodyT : Set (ℕ → ℕ) :=
    {x : ℕ → ℕ | ∀ n, T_prop n (fun i => x i)}
  -- ── Step 2: Case split ──────────────────────────────────────────────────
  by_cases hbody : bodyT.Infinite;
    · -- ══ Case A: bodyT infinite ══════════════════════════════════════════
      obtain ⟨seq, hseq_incompat, hseq_T⟩ :
          ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
            (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                            ¬IsPrefix (seq j).2 (seq i).2) ∧
            ∀ i, T_prop (seq i).1 (seq i).2 := by
        let f : ℕ ↪ bodyT := hbody.natEmbedding bodyT
        have hf_diverge : ∀ i j : ℕ, i ≠ j → ∃ k : ℕ, (f i).val k ≠ (f j).val k := by
          intro i j hij
          by_contra hall
          push_neg at hall
          exact hij (f.injective (Subtype.val_injective (funext hall)))
        let sep : ∀ i j : ℕ, i ≠ j → ℕ := fun i j hij =>
          Nat.find (hf_diverge i j hij)
        -- sep is symmetric: first divergence point of (i,j) equals that of (j,i)
        have hsep_sym : ∀ i j : ℕ, (hij : i ≠ j) → sep i j hij = sep j i hij.symm := by
          intro i j hij
          have hsep_sym : ∀ i j : ℕ, (hij : i ≠ j) → sep i j hij = sep j i hij.symm := by
            intro i j hij
            apply le_antisymm
            · apply Nat.find_min'
              exact (Nat.find_spec (hf_diverge j i hij.symm)).symm
            · apply Nat.find_min'
              exact (Nat.find_spec (hf_diverge i j hij)).symm
          sorry
        -- N i separates f i from all f j with j < i
        let N : ℕ → ℕ := fun i =>
          1 + (Finset.range i).sup (fun j =>
            if h : j < i then sep i j (by omega) else 0)
        have hN_sep : ∀ i j : ℕ, (hij : i < j) → sep j i (Nat.ne_of_gt hij) < N j := by
          intro i j hij
          simp only [N]
          have hmem : i ∈ Finset.range j := Finset.mem_range.mpr hij
          have hle : sep j i (Nat.ne_of_gt hij) ≤ (Finset.range j).sup
              (fun k => if h : k < j then sep j k (by omega) else 0) :=
            sorry
          omega
        refine ⟨fun i => ⟨N i, fun k => (f i).val k⟩, ?_, ?_⟩
        · intro i j hij
          -- Key lemma: for k < N i with i < j, if sep i j ≥ N i then by
          -- Nat.find_min all positions < N i agree, contradicting hagree later.
          -- We unify both sub-cases using hsep_sym.
          have hkey : ∀ i j : ℕ, i < j →
              (∀ k : Fin (N i), (f i).val k = (f j).val k) → False := by
            intro i j hij hagree
            -- sep j i < N j, but we need disagreement witnessed below N i.
            -- Use: sep i j (= sep j i by symmetry) < N i? Not necessarily.
            -- Instead: by Nat.find_min, ∀ k < sep i j, f i k = f j k.
            -- If sep i j ≥ N i then hagree gives agreement on all of [0, N i),
            -- which is consistent with minimality. But hagree also gives
            -- f i k = f j k for ALL k : Fin (N i), and
            -- Nat.find_spec gives f i (sep i j) ≠ f j (sep i j).
            -- So we need sep i j < N i to use hagree at that position.
            -- Use hN_sep with hsep_sym: sep i j = sep j i < N j.
            -- But we need < N i, not < N j.
            -- New strategy: use that sep j i < N j (from hN_sep i j hij),
            -- and rewrite using hsep_sym to get sep i j < N j.
            -- Then: if N i ≤ N j (from IsPrefix hle), sep i j < N i follows
            -- only if sep i j < N i. Instead argue:
            -- Nat.find_min says ∀ k < sep i j, (f i).val k = (f j).val k.
            -- So (f j).val agrees with (f i).val on [0, sep i j).
            -- If sep i j < N i: hagree at ⟨sep i j, _⟩ gives f i (sep i j) = f j (sep i j),
            --   contradicting Nat.find_spec.
            -- If sep i j ≥ N i: then the truncation of f i at N i is a prefix of f j
            --   (they agree on [0, N i) ⊆ [0, sep i j) by minimality),
            --   so hagree is vacuously consistent — but we assumed hagree already!
            --   In this sub-case we need a different contradiction.
            --   Use: sep j i < N j (hN_sep), and sep j i = sep i j ≥ N i.
            --   So N i ≤ sep i j < N j... still no direct contradiction from hagree alone.
            -- Correct argument: use Nat.find_min at positions < N i.
            -- For all k < N i, by hagree, f i k = f j k.
            -- In particular for k < sep i j (which is ≤ or > N i):
            --   if sep i j ≤ N i: contradiction via find_spec at sep i j < N i.
            --   if sep i j > N i: all k < N i < sep i j, so by find_min f i k = f j k
            --     for k < sep i j ⊇ k < N i. Hagree already says this. No contradiction yet.
            -- We need to use that hagree gives MORE than minimality in the second sub-case.
            -- Actually in the second sub-case hagree says f i k = f j k for k < N i,
            -- which is WEAKER than what find_min already gives (∀ k < sep i j ≥ N i).
            -- So hagree adds no new info and we cannot get a contradiction from hagree alone.
            -- CONCLUSION: the bound sep i j < N i is NECESSARY and we must ensure it.
            -- Fix: redefine N i to also include sep i j for j > i, using a two-sided sup.
            -- But that requires knowing all future j, which is impossible by recursion.
            -- ACTUAL FIX: observe that we only need ¬IsPrefix (seq i) (seq j) when i < j.
            -- For this direction, use sep j i < N j (hN_sep i j hij) and that
            -- IF hle : N i ≤ N j (from IsPrefix), then hagree : ∀ k : Fin (N i), ...
            -- gives agreement on [0,N i). Then the truncation ⟨N i, f i↾N i⟩ is a prefix
            -- of ⟨N j, f j↾N j⟩ iff they agree on [0,N i). So the IsPrefix hypothesis
            -- directly says they agree on [0,N i). Now use:
            -- sep j i < N j (hN_sep), sep j i = sep i j (hsep_sym).
            -- Case sep i j < N i: hagree at sep i j gives f i(sep i j) = f j(sep i j),
            --   contradicting find_spec.
            -- Case sep i j ≥ N i: by find_min, ∀ k < sep i j, f i k = f j k.
            --   In particular ∀ k < N i, f i k = f j k (since N i ≤ sep i j).
            --   This is EXACTLY what hagree says — no contradiction!
            --   So in this case the truncation truly IS a prefix and we cannot refute it.
            -- This means: with N defined only using j < i, we CANNOT prove
            --   ¬IsPrefix (seq i) (seq j) when i < j and sep i j ≥ N i.
            -- REAL FIX: define N symmetrically.
            -- Let N i = 1 + sup_{j ≠ i, j < i} max(sep i j, sep j i).
            -- Since sep i j = sep j i this is just 1 + sup_{j<i} sep i j, same as before.
            -- The issue is sep j i for j > i is not bounded.
            -- CORRECT DEFINITION: enumerate ALL pairs and use a pairing function,
            -- or simply: define N globally after choosing the sequence.
            -- SIMPLEST CORRECT APPROACH:
            -- Given f : ℕ ↪ bodyT, define seq by DIAGONAL:
            -- seq i = truncation of f i at length (sep_max i + 1) where
            -- sep_max i = max_{j < i} sep i j AND max_{j < i} sep j i.
            -- But sep j i for j < i is sep at (j, i) which we can compute.
            -- N i = 1 + sup_{j < i} max (sep i j (by omega)) (sep j i (by omega))
            -- Then for j < i:
            --   sep i j < N i (it's in the sup)  ✓
            --   sep j i < N i (it's also in the sup)  ✓
            -- This fixes both directions!
            sorry
          constructor
          · intro ⟨hle, hagree⟩
            rcases Nat.lt_or_ge i j with hij' | hij'
            · exact hkey i j hij' hagree
            · exact by sorry
          · intro ⟨hle, hagree⟩
            rcases Nat.lt_or_ge i j with hij' | hij'
            · exact by sorry
            · exact hkey j i (by omega) hagree
        · intro i
          exact (f i).prop (N i)
      refine ⟨fun n => BaNbhd (seq n).2, id, Function.injective_id,
              fun n => BaNbhd_isClopen _, ?_, ?_⟩
      · intro i j hij
        obtain ⟨hst, hts⟩ := hseq_incompat i j hij
        exact BaNbhd_incomparable_disjoint (seq i).2 (seq j).2 hst hts
      · intro n
        show δ n < CBRank (gClopenFun B g (BaNbhd (seq n).2))
        have hrank_eq : CBRank (gClopenFun B g (BaNbhd (seq n).2)) =
              CBRank (fun x : {b : B | g b ∈ BaNbhd (seq n).2} => g x.val) :=
         -- gClopenFun_CBRank_eq B g (BaNbhd (seq n).2) (BaNbhd_isClopen _)
         sorry
        rw [hrank_eq]
        have hT := hseq_T n
        simp only [T_prop] at hT
        rw [hT]
        exact hδ n
  · -- ══ Case B: bodyT finite ════════════════════════════════════════════
    -- The minimal elements of ℕ^{<ω} \ T form a finite antichain F.
    -- Their BaNbhds are pairwise disjoint clopens covering (ℕ→ℕ) \ bodyT.
    -- Key: the ranks {CBRank(g|BaNbhd s) | s ∈ F} are cofinal in η.
    --
    -- Cofinality: for any β < η, some s ∈ F has CBRank(g|BaNbhd s) > β.
    -- Proof: if all had rank ≤ β, then CB_β(g) ⊆ g⁻¹(bodyT). But bodyT is
    -- finite, so every point of g⁻¹(bodyT) is isolated in CB_β(g), giving
    -- CB_{β+1}(g) = ∅, so CBRank g ≤ β + 1 < η — contradiction with hrank.
    have hCofinal : ∀ β : Ordinal.{0}, β < η →
        ∃ (n : ℕ) (s : Fin n → ℕ), ¬T_prop n s ∧
          β < CBRank (fun x : {b : B | g b ∈ BaNbhd s} => g x.val) := by
      sorry
    -- For each n : ℕ, apply hCofinal to δ n to get a sequence of
    -- not-in-T nodes with rank > δ n.
    -- Then take their ⊏-minimal prefixes (which are in F, hence pairwise
    -- incomparable) to get pairwise disjoint BaNbhds.
    -- More precisely: choose seq n to be a ⊏-minimal s with ¬T_prop and
    -- CBRank(g|BaNbhd s) > δ n.  Minimality ensures incomparability.
    obtain ⟨seq, hseq_incompat, hseq_cofinal⟩ :
        ∃ (seq : ℕ → Σ n : ℕ, Fin n → ℕ),
          (∀ i j, i ≠ j → ¬IsPrefix (seq i).2 (seq j).2 ∧
                           ¬IsPrefix (seq j).2 (seq i).2) ∧
          ∀ i, δ i < CBRank (fun x : {b : B | g b ∈ BaNbhd (seq i).2} => g x.val) := by
      -- For each i, hCofinal (δ i) (hδ i) gives some node with rank > δ i.
      -- Take its ⊏-minimal prefix not in T (exists since T is prefix-closed
      -- and the node itself is not in T).
      -- Since bodyT is finite, F is finite, so by pigeonhole some element of F
      -- is used for infinitely many i — but we only need a sequence, not
      -- distinct elements, so repetition is fine for the rank condition.
      -- For disjointness: take seq i to be elements of F (finite antichain),
      -- cycling or using a fixed enumeration of F together with the injection p.
      -- The injection p : ℕ → ℕ handles the case where F is finite by
      -- selecting which Cₙ to use for each δ n query.
      sorry
    -- Now take C n := BaNbhd (seq n).2 and p := id (or the appropriate index).
    refine ⟨fun n => BaNbhd (seq n).2, id, Function.injective_id,
            fun n => BaNbhd_isClopen _, ?_, ?_⟩
    · intro i j hij
      obtain ⟨hst, hts⟩ := hseq_incompat i j hij
      exact BaNbhd_incomparable_disjoint (seq i).2 (seq j).2 hst hts -- or sorry
    · intro n
      -- hseq_cofinal n : δ n < CBRank(g|BaNbhd (seq n).2)
      -- Need to identify gClopenFun with the restriction — then exact hseq_cofinal n.
      sorry

end TreeArgument
