module

public import Theory.GroupTheory.ChiefFactorDirectPower
public import Mathlib.Order.Sublattice
public import Mathlib.Order.JordanHolder
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Refining finite ambient-normal filtrations

Normal subgroups form a modular lattice: write an element of a join as a
product and use the containment in the modular identity to recover the second
factor. Covering in this lattice is exactly `ChiefFactor.IsChief`, with both
endpoints normal in the ambient group.

Finite-order refinement and concatenation construct chief series, including
filtrations with repeated terms. Every chief interval occurs in a complete
series. Mathlib's abstract Jordan–Hölder theorem then applies to this lattice;
its interval relation still needs an equivariant quotient interpretation.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.5(8), printed pp.335–336. The order-theoretic construction is source-neutral.
-/

@[expose] public section

open Subgroup
namespace NoncentralChiefRefinement
variable (K : Type*) [Group K]

/-- Ambient normal subgroups form a sublattice of the subgroup lattice. -/
def normalSublattice : Sublattice (Subgroup K) where
  carrier := {N | N.Normal}
  supClosed' := by
    intro A hA B hB
    let : A.Normal := hA
    let : B.Normal := hB
    exact inferInstanceAs (A ⊔ B).Normal
  infClosed' := by
    intro A hA B hB
    let : A.Normal := hA
    let : B.Normal := hB
    exact inferInstanceAs (A ⊓ B).Normal

/-- A subgroup together with normality in the fixed ambient group. -/
abbrev NormalNode := ↥(normalSublattice K)

instance normalNode_normal (N : NormalNode K) : N.val.Normal := N.property

instance normalNode_boundedOrder : BoundedOrder (NormalNode K) where
  top := ⟨⊤, inferInstanceAs (⊤ : Subgroup K).Normal⟩
  le_top _ := le_top (α := Subgroup K)
  bot := ⟨⊥, inferInstanceAs (⊥ : Subgroup K).Normal⟩
  bot_le _ := bot_le (α := Subgroup K)

instance normalNode_isModularLattice : IsModularLattice (NormalNode K) where
  sup_inf_le_assoc_of_le := by
    intro A B C hAC x hx
    change x ∈ (A.val ⊔ B.val) ⊓ C.val at hx
    change x ∈ A.val ⊔ (B.val ⊓ C.val)
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.mp hx.1
    have hbc : b ∈ C.val := by
      have hh := C.val.mul_mem (C.val.inv_mem (hAC ha)) hx.2
      simpa only [inv_mul_cancel_left] using hh
    exact mul_mem_sup ha ⟨hb, hbc⟩

variable {K}

/-- Covering in this lattice is exactly ambient chiefness. -/
theorem covBy_iff_isChief (A B : NormalNode K) :
    A ⋖ B ↔ ChiefFactor.IsChief B.val A.val := by
  constructor
  · intro h
    refine ⟨inferInstance, inferInstance, h.lt, ?_⟩
    intro Z hZ hAZ hZB
    by_cases he : Z = A.val
    · exact Or.inl he
    right
    obtain hc | hc := h.eq_or_eq (c := ⟨Z, hZ⟩) hAZ hZB
    · exact (he (congrArg Subtype.val hc)).elim
    · exact congrArg Subtype.val hc
  · intro h
    refine ⟨h.lt, ?_⟩
    intro Z hAZ hZB
    obtain he | he := h.minimal Z.val Z.property hAZ.le hZB.le
    · exact hAZ.ne (Subtype.ext he.symm)
    · exact hZB.ne (Subtype.ext he)

/-- A finite series whose successive intervals are ambient chief intervals. -/
abbrev ChiefSeries (K : Type*) [Group K] := CompositionSeries (NormalNode K)

/-- Every step uses the existing chief-factor convention. -/
theorem ChiefSeries.isChief (s : ChiefSeries K) (i : Fin s.length) :
    ChiefFactor.IsChief (s i.succ).val (s i.castSucc).val :=
  (covBy_iff_isChief _ _).mp (s.step i)

/-- Every finite normal interval has a chief series. -/
theorem exists_chiefSeries [Finite K] (A B : NormalNode K) (hAB : A ≤ B) :
    ∃ s : ChiefSeries K, s.head = A ∧ s.last = B := by
  obtain ⟨a, ha, n, hn, hstep⟩ :=
    exists_covBy_seq_of_wellFoundedLT_wellFoundedGT_of_le hAB
  exact ⟨⟨n, fun i => a i, fun i => hstep i i.isLt⟩, ha, hn⟩

/-- Abstract Jordan–Hölder equivalence in the normal-subgroup lattice.
Transport of this relation to equivariant quotient isomorphisms is separate. -/
theorem chiefSeries_jordanHolder (s t : ChiefSeries K)
    (hhead : s.head = t.head) (hlast : s.last = t.last) : s.Equivalent t :=
  CompositionSeries.jordan_holder s t hhead hlast

/-- A finite normal filtration may have repeated terms. -/
structure Filtration (K : Type*) [Group K] (n : ℕ) where
  term : Fin (n + 1) → NormalNode K
  monotone : Monotone term

private theorem exists_refinement_terms [Finite K] {n : ℕ} (f : Filtration K n) :
    ∃ s : ChiefSeries K, s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      ∀ i, ∃ j, s j = f.term i := by
  induction n with
  | zero =>
    refine ⟨RelSeries.singleton _ (f.term 0), rfl, rfl, ?_⟩
    intro i
    exact ⟨0, congrArg f.term (Fin.ext (by omega))⟩
  | succ n ih =>
    let f' : Filtration K n := ⟨fun i => f.term i.castSucc,
      fun _ _ h => f.monotone h⟩
    obtain ⟨s, hs0, hsl, hs⟩ := ih f'
    obtain ⟨t, ht0, htl⟩ := exists_chiefSeries
      (f.term (Fin.last n).castSucc) (f.term (Fin.last (n + 1)))
      (f.monotone (Fin.le_last _))
    have hst : s.last = t.head := hsl.trans ht0.symm
    refine ⟨s.smash t hst, ?_, ?_, ?_⟩
    · simpa [f'] using hs0
    · simpa only [RelSeries.last_smash] using htl
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · exact ⟨Fin.last _, (RelSeries.last_smash hst).trans htl⟩
    · obtain ⟨j, hj⟩ := hs i
      exact ⟨j.castLE (by simp), (RelSeries.smash_castLE hst j).trans hj⟩

/-- Every finite normal filtration has a refinement by actual chief intervals.
Repeated coarse terms, including zero-dimensional strata, share an index. -/
theorem exists_refinement [Finite K] {n : ℕ} (f : Filtration K n) :
    ∃ (s : ChiefSeries K) (ι : Fin (n + 1) →o Fin (s.length + 1)),
      (∀ i, s (ι i) = f.term i) ∧ ι 0 = 0 ∧ ι (Fin.last n) = Fin.last s.length := by
  classical
  obtain ⟨s, hs0, hsl, hs⟩ := exists_refinement_terms f
  let j := fun i => (hs i).choose
  have hj : ∀ i, s (j i) = f.term i := fun i => (hs i).choose_spec
  let ι : Fin (n + 1) →o Fin (s.length + 1) :=
    ⟨j, fun i k hik => s.strictMono.le_iff_le.mp (by rw [hj, hj]; exact f.monotone hik)⟩
  refine ⟨s, ι, hj, ?_, ?_⟩
  · exact s.injective ((hj 0).trans hs0.symm)
  · exact s.injective ((hj (Fin.last n)).trans hsl.symm)

/-- A partial chief series extends to the whole group, preserving every term.
No assertion about the terminal factors is needed for this existence theorem. -/
theorem ChiefSeries.exists_extension [Finite K] (s : ChiefSeries K) :
    ∃ t : ChiefSeries K, t.head = s.head ∧ t.last = ⊤ ∧
      ∃ ι : Fin (s.length + 1) ↪ Fin (t.length + 1), ∀ i, t (ι i) = s i := by
  obtain ⟨u, hu0, hul⟩ := exists_chiefSeries s.last ⊤ le_top
  let hsu : s.last = u.head := hu0.symm
  refine ⟨s.smash u hsu, RelSeries.head_smash hsu,
    (RelSeries.last_smash hsu).trans hul, ?_⟩
  refine ⟨⟨fun i => i.castLE (by simp), ?_⟩, fun i => RelSeries.smash_castLE hsu i⟩
  intro i j hij
  exact Fin.ext (congrArg (fun k : Fin (s.length + u.length + 1) => k.val) hij)

/-- Every actual chief interval occurs in a complete chief series. Combined
with equivariant Jordan–Hölder, this justifies statements about all chief
factors of the group rather than about one chosen series. -/
theorem exists_complete_chiefSeries_containing [Finite K] (A B : NormalNode K)
    (hAB : A ⋖ B) :
    ∃ s : ChiefSeries K, s.head = ⊥ ∧ s.last = ⊤ ∧
      ∃ i : Fin s.length, s i.castSucc = A ∧ s i.succ = B := by
  obtain ⟨s, hs0, hsl⟩ := exists_chiefSeries ⊥ A bot_le
  have hstep : s.last ⋖ B := hsl ▸ hAB
  let s' : ChiefSeries K := s.snoc B hstep
  obtain ⟨t, ht0, htl⟩ := exists_chiefSeries B ⊤ le_top
  have hst : s'.last = t.head := (RelSeries.last_snoc s B hstep).trans ht0.symm
  refine ⟨s'.smash t hst, ?_, ?_, (Fin.last s.length).castAdd t.length, ?_, ?_⟩
  · simpa only [s', RelSeries.head_smash, RelSeries.head_snoc] using hs0
  · exact (RelSeries.last_smash hst).trans htl
  · exact (RelSeries.smash_castAdd (p := s') (q := t) hst (Fin.last s.length)).trans
      ((RelSeries.snoc_castSucc s B hstep (Fin.last s.length)).trans hsl)
  · exact (RelSeries.smash_succ_castAdd (p := s') (q := t) hst (Fin.last s.length)).trans
      (RelSeries.last_snoc' s B hstep)


end NoncentralChiefRefinement
