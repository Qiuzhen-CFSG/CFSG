module

public import Theory.GroupTheory.NoncentralChiefRefinement.Homogeneous
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport

/-!
# Chief-factor accounting from an actual normal filtration

Refine each central or homogeneous binary stratum, then concatenate the
refinements. Every coarse term survives in order, and noncentral two-chief
counts add to the sum of the supplied multiplicities. The factors retain
one-copy equivariant coordinates for the specified representation.

If the literal quotient above the endpoint has no two-chief factors, extend
the series to the whole group without adding to the count. Equivariant
Jordan–Hölder transfers both the count and the marked action to every complete
chief series. Inserting any given chief interval into such a series establishes
the assertion for all actual chief factors, not just a numerical invariant.
The endpoint need not be a two-group; in particular the result applies to a
filtration from 1 to a normal two-subgroup.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.5(8), printed pp.335–336 (PDF pp.346–347). Constructing the source filtration
and its equivariant coordinates is separate from this source-neutral argument.
-/

public section

open Subgroup
namespace NoncentralChiefRefinement
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) K V}

private theorem forall_factors_smash (s t : ChiefSeries K) (hst : s.last = t.head)
    (P : NormalNode K → NormalNode K → Prop)
    (hs : ∀ i : Fin s.length, P (s i.castSucc) (s i.succ))
    (ht : ∀ i : Fin t.length, P (t i.castSucc) (t i.succ)) :
    ∀ i : Fin (s.smash t hst).length,
      P ((s.smash t hst) i.castSucc) ((s.smash t hst) i.succ) := by
  intro i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · exact (congrArg₂ P (RelSeries.smash_castAdd hst j)
      (RelSeries.smash_succ_castAdd hst j)).mpr (hs j)
  · exact (congrArg₂ P (RelSeries.smash_natAdd hst j)
      (RelSeries.smash_succ_natAdd hst j)).mpr (ht j)

private theorem exists_marked_refinement_terms [Finite K] [Representation.IsIrreducible ρ]
    (hρ : ∃ k v, ρ k v ≠ v) {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i)) :
    ∃ s : ChiefSeries K, s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      s.noncentralTwoCount = ∑ i, m i ∧
      (∀ i, ∃ j, s j = f.term i) ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  induction n with
  | zero =>
    refine ⟨RelSeries.singleton _ (f.term 0), rfl, rfl, ?_, ?_, ?_⟩
    · simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun i => Fin.elim0 i.val⟩)
    · intro i
      exact ⟨0, congrArg f.term (Fin.ext (by omega))⟩
    · exact fun i => Fin.elim0 i
  | succ n ih =>
    let f' : Filtration K n := ⟨fun i => f.term i.castSucc, fun _ _ h => f.monotone h⟩
    obtain ⟨s, hs0, hsl, hsc, hs, hsa⟩ :=
      ih f' (fun i => m i.castSucc) (fun i => hf i.castSucc)
    obtain ⟨t, ht0, htl, htc, hta⟩ :=
      (hf (Fin.last n)).exists_chief_refinement (f.monotone (Fin.castSucc_le_succ _)) hρ
    have hst : s.last = t.head := hsl.trans ht0.symm
    refine ⟨s.smash t hst, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [RelSeries.head_smash, f', Fin.castSucc_zero] using hs0
    · simpa only [RelSeries.last_smash, Fin.succ_last] using htl
    · rw [ChiefSeries.noncentralTwoCount_smash, hsc, htc, Fin.sum_univ_castSucc]
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact ⟨Fin.last _, (RelSeries.last_smash hst).trans htl⟩
      · obtain ⟨j, hj⟩ := hs i
        exact ⟨j.castLE (by simp), (RelSeries.smash_castLE hst j).trans hj⟩
    · exact forall_factors_smash s t hst
        (fun A B => IsNoncentralTwo A B → Nonempty (SectionCoordinates A B ρ 1)) hsa hta

/-- A normal filtration with central or homogeneous binary strata has an
actual chief refinement, retaining every coarse term, the sum of multiplicities,
and the specified conjugation action on every noncentral two-chief factor.
Repeated terms and zero multiplicities are allowed. -/
theorem Filtration.exists_marked_refinement [Finite K] [Representation.IsIrreducible ρ]
    {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i))
    (hρ : ∃ k v, ρ k v ≠ v) :
    ∃ (s : ChiefSeries K) (ι : Fin (n + 1) →o Fin (s.length + 1)),
      (∀ i, s (ι i) = f.term i) ∧ ι 0 = 0 ∧ ι (Fin.last n) = Fin.last s.length ∧
      s.head = f.term 0 ∧ s.last = f.term (Fin.last n) ∧
      s.noncentralTwoCount = ∑ i, m i ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  classical
  obtain ⟨s, hs0, hsl, hsc, hs, hsa⟩ := exists_marked_refinement_terms hρ f m hf
  let j := fun i => (hs i).choose
  have hj : ∀ i, s (j i) = f.term i := fun i => (hs i).choose_spec
  let ι : Fin (n + 1) →o Fin (s.length + 1) :=
    ⟨j, fun i k hik => s.strictMono.le_iff_le.mp (by rw [hj, hj]; exact f.monotone hik)⟩
  refine ⟨s, ι, hj, ?_, ?_, hs0, hsl, hsc, hsa⟩
  · exact s.injective ((hj 0).trans hs0.symm)
  · exact s.injective ((hj (Fin.last n)).trans hsl.symm)

/-- Count and actions pass to every chief series with the same endpoints.
The matching is by equivariant isomorphisms of the literal quotient factors. -/
theorem ChiefSeries.marked_of_same_endpoints (s t : ChiefSeries K)
    (hhead : s.head = t.head) (hlast : s.last = t.last)
    (hs : ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
      Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1)) :
    t.noncentralTwoCount = s.noncentralTwoCount ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (SectionCoordinates (t i.castSucc) (t i.succ) ρ 1) := by
  obtain ⟨e, he⟩ := t.exists_sectionEquiv_matching s hhead.symm hlast.symm
  refine ⟨t.noncentralTwoCount_eq_of_matching s e he, ?_⟩
  intro i hi
  obtain ⟨ei⟩ := he i
  obtain ⟨c⟩ := hs (e i) (ei.isNoncentralTwo_iff.mp hi)
  exact ⟨c.transport ei⟩

/-- Extend the refinement to the whole group. The terminal premise concerns
all actual two-chief intervals in the literal quotient, including central ones.
No two-group assumption on the endpoint is needed for this stronger statement. -/
theorem Filtration.exists_complete_marked_refinement [Finite K]
    [Representation.IsIrreducible ρ] {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i))
    (hρ : ∃ k v, ρ k v ≠ v) (h0 : f.term 0 = ⊥)
    (hterminal : HasNoTwoChiefFactors (K ⧸ (f.term (Fin.last n)).val)) :
    ∃ (s : ChiefSeries K) (ι : Fin (n + 1) →o Fin (s.length + 1)),
      (∀ i, s (ι i) = f.term i) ∧ ι 0 = 0 ∧ s.head = ⊥ ∧ s.last = ⊤ ∧
      s.noncentralTwoCount = ∑ i, m i ∧
      ∀ i : Fin s.length, IsNoncentralTwo (s i.castSucc) (s i.succ) →
        Nonempty (SectionCoordinates (s i.castSucc) (s i.succ) ρ 1) := by
  obtain ⟨s, ι, hι, hι0, _, hs0, hsl, hsc, hsa⟩ := f.exists_marked_refinement m hf hρ
  obtain ⟨t, ht0, htl⟩ := exists_chiefSeries (f.term (Fin.last n)) ⊤ le_top
  have hst : s.last = t.head := hsl.trans ht0.symm
  let j : Fin (n + 1) →o Fin ((s.smash t hst).length + 1) :=
    ⟨fun i => (ι i).castLE (by simp), fun _ _ h => ι.monotone h⟩
  refine ⟨s.smash t hst, j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (RelSeries.smash_castLE hst (ι i)).trans (hι i)
  · apply Fin.ext
    change (ι 0).val = 0
    rw [hι0]
    rfl
  · exact (RelSeries.head_smash hst).trans (hs0.trans h0)
  · exact (RelSeries.last_smash hst).trans htl
  · rw [ChiefSeries.noncentralTwoCount_smash, hsc,
      t.noncentralTwoCount_eq_zero_of_quotient _ ht0.ge hterminal, add_zero]
  · apply forall_factors_smash s t hst
      (fun A B => IsNoncentralTwo A B → Nonempty (SectionCoordinates A B ρ 1)) hsa
    intro i hi
    exact (not_isPGroup_section_of_quotient _ hterminal (t.step i)
      (ht0.ge.trans (CompositionSeries.head_le i.castSucc)) hi.1).elim

/-- Every complete chief series has the computed count and specified actions,
not just the specially constructed refinement. -/
theorem Filtration.complete_series_accounting [Finite K]
    [Representation.IsIrreducible ρ] {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i))
    (hρ : ∃ k v, ρ k v ≠ v) (h0 : f.term 0 = ⊥)
    (hterminal : HasNoTwoChiefFactors (K ⧸ (f.term (Fin.last n)).val))
    (t : ChiefSeries K) (ht0 : t.head = ⊥) (htl : t.last = ⊤) :
    t.noncentralTwoCount = ∑ i, m i ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (SectionCoordinates (t i.castSucc) (t i.succ) ρ 1) := by
  obtain ⟨s, _, _, _, hs0, hsl, hsc, hsa⟩ :=
    f.exists_complete_marked_refinement m hf hρ h0 hterminal
  obtain ⟨hc, ha⟩ := s.marked_of_same_endpoints t (hs0.trans ht0.symm) (hsl.trans htl.symm) hsa
  exact ⟨hc.trans hsc, ha⟩

/-- Every actual noncentral two-chief interval of the group carries the given
action: insert it into a complete series and apply equivariant Jordan–Hölder. -/
theorem Filtration.chief_factor_coordinates [Finite K]
    [Representation.IsIrreducible ρ] {n : ℕ} (f : Filtration K n) (m : Fin n → ℕ)
    (hf : ∀ i, IsModuleStratum ρ (f.term i.castSucc) (f.term i.succ) (m i))
    (hρ : ∃ k v, ρ k v ≠ v) (h0 : f.term 0 = ⊥)
    (hterminal : HasNoTwoChiefFactors (K ⧸ (f.term (Fin.last n)).val))
    (A B : NormalNode K) (hAB : ChiefFactor.IsChief B.val A.val)
    (hp : IsPGroup 2 (Section A B)) (hn : ¬ IsCentral A B) :
    Nonempty (SectionCoordinates A B ρ 1) := by
  obtain ⟨s, hs0, hsl, i, hi0, hi1⟩ :=
    exists_complete_chiefSeries_containing A B ((covBy_iff_isChief A B).mpr hAB)
  have ha := (f.complete_series_accounting m hf hρ h0 hterminal s hs0 hsl).2 i
  rw [hi0, hi1] at ha
  exact ha ⟨hp, hn⟩

end NoncentralChiefRefinement
