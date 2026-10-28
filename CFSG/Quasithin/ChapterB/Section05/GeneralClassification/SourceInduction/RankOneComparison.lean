module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.ModelRank
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Comparing the recursive alternatives at three-rank one

Each actual factor in B.5.6(3) and (5) has a cubic subgroup, so its internal
product has three-rank at least two. The outer shape contains the actual A₆
factor, also of three-rank at least two. Consequently the complete adequate
classification at rank at most one leaves precisely its quasisimple and S₃
branches. In the quasisimple branch we retain every B.5.1 clause and additionally
apply the proved exhaustive rank-one comparison to its actual moved section.

These are implications from a classification already proved at a smaller order;
they supply no unrestricted classifier. B.5.8 and B.5.11 are their consumers.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.106 and 109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource

private theorem positive_three_rank {D : Type*} [Group D] [Finite D]
    (h : 3 ∣ Nat.card D) : 0 < primeRank 3 D :=
  Nat.pos_of_ne_zero (fun he => PrimeRank.eq_zero_iff_not_dvd_card.mp he h)

private theorem linear_three_rank_pos (F : BinaryField) {d : ℕ} (hd : 2 ≤ d) :
    0 < primeRank 3 (Matrix.SpecialLinearGroup (Fin d) F.Carrier) := by
  have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
    (F := F.Carrier) (i := (⟨0, by omega⟩ : Fin d)) (j := (⟨1, by omega⟩ : Fin d))
    (Fin.ne_of_val_ne (by change (0 : ℕ) ≠ 1; decide))
  apply positive_three_rank
  exact (h3.trans (card_subgroup_dvd_card _)).trans
    (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center
      (Matrix.SpecialLinearGroup (Fin d) F.Carrier)))
      (QuotientGroup.mk'_surjective _))

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

/-- Every natural factor includes an actual group identification, which gives
positive three-rank independently of the dimension of the ambient module. -/
theorem FactorNatural.three_rank_pos (h : FactorNatural ρ) : 0 < primeRank 3 D := by
  cases h with
  | linearTwo F h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos F (by decide)
  | symmetricFive h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      apply positive_three_rank
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  | linearThree F _ h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos F (by decide)

/-- Both exceptional and doubled factor actions retain a cubic actor. -/
theorem SourceFactorCase.three_rank_pos {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : 0 < primeRank 3 A := by
  cases h with
  | natural _ h => exact h.three_rank_pos
  | doubleNatural F _ _ h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos F (by decide)
  | exceptional _ h =>
      rw [primeRank_equiv 3 h.natural.groupEquiv]
      exact linear_three_rank_pos BinaryField.two (by decide)

/-- The two actual subgroup inclusions force three-rank at least two. -/
theorem SourceTwoFactorCase.two_le_three_rank (h : SourceTwoFactorCase ρ) :
    2 ≤ primeRank 3 D := by
  have ha := h.firstCase.three_rank_pos
  have hb := h.secondCase.three_rank_pos
  rw [← primeRank_equiv 3 h.product.equiv, primeRank_prod_eq_add]
  omega

/-- Even a zero multiplicity in the module contract retains its specified
SL₃ actor; the group identification is never replaced by a dimension tag. -/
theorem HyperplaneSecondCase.three_rank_pos {A : Subgroup D} {U : Subrepresentation ρ}
    (h : HyperplaneSecondCase ρ A U) : 0 < primeRank 3 A := by
  cases h with
  | linearThree r _ h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos BinaryField.two (by decide)
  | linearTwo F h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos F (by decide)

/-- The exceptional hyperplane alternative also has two independent cubic factors. -/
theorem HyperplaneCase.two_le_three_rank (h : HyperplaneCase ρ) :
    2 ≤ primeRank 3 D := by
  have ha : 0 < primeRank 3 h.first := by
    rw [primeRank_equiv 3 h.firstEquiv]
    exact linear_three_rank_pos BinaryField.two (by decide)
  have hb := h.secondCase.three_rank_pos
  rw [← primeRank_equiv 3 h.product.equiv, primeRank_prod_eq_add]
  omega

/-- The group-only outer alternative is already excluded by its literal A₆ factor. -/
theorem outerShape_two_le_three_rank (h : OuterSixThreeShape D) :
    2 ≤ primeRank 3 D := by
  have ha := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
  rw [← primeRank_equiv 3 h.firstEquiv] at ha
  exact ha.trans (primeRank_le_of_injective 3 h.first.subtype h.first.subtype_injective)

/-- The comparison used after each legitimate recursive classification in
B.5.8 and B.5.11. All module clauses in the surviving alternatives are retained. -/
theorem NontrivialAdequateAlternative.at_three_rank_le_one
    (h : NontrivialAdequateAlternative ρ) (hr : primeRank 3 D ≤ 1) :
    (IsQuasisimple (generalizedFitting D) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D))) ∨
      Nonempty (SymmetricThreeCase ρ) := by
  cases h with
  | quasisimple hq c => exact Or.inl ⟨hq, ⟨c⟩⟩
  | symmetricThree c => exact Or.inr ⟨c⟩
  | twoFactors c => have := c.two_le_three_rank; omega
  | outerSixThree c => have := outerShape_two_le_three_rank c; omega
  | hyperplane c => have := c.two_le_three_rank; omega

/-- The same comparison, removing only the genuinely trivial actor. -/
theorem AdequateAlternative.at_three_rank_le_one [Nontrivial D]
    (h : AdequateAlternative ρ) (hr : primeRank 3 D ≤ 1) :
    (IsQuasisimple (generalizedFitting D) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D))) ∨
      Nonempty (SymmetricThreeCase ρ) :=
  (h.of_nontrivial ρ).at_three_rank_le_one hr

private theorem quasisimple_action_three_rank_pos {L : Subgroup D}
    {s : MovedSection ρ L} (c : ProjectiveLine.QuasisimpleActionCase ρ L s) :
    0 < primeRank 3 L := by
  cases c with
  | irreducible _ _ _ c _ => exact HighThreeRank.CoverCentralizer.action_case_rank_pos c
  | doubleThree F _ e _ _ =>
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos F (by decide)
  | naturalDual d hd _ h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos BinaryField.two (by omega)
  | repeatedNatural d r hd _ _ _ h =>
      obtain ⟨e⟩ := h
      rw [primeRank_equiv 3 e.groupEquiv]
      exact linear_three_rank_pos BinaryField.two (by omega)

/-- The retained full B.5.1 conclusion has exactly the three rank-one natural
rows or the doubled SL₃ row on its literal moved section. The remaining
extension and supplement clauses remain available in `c`. -/
theorem ProjectiveLine.QuasisimpleSourceConclusion.rank_one_action
    {L : Subgroup D} (c : ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hr : primeRank 3 D ≤ 1) :
    ComponentReduction.PreliminaryActions.RankOneActionCase ρ L c.sectionData := by
  have hpos := quasisimple_action_three_rank_pos c.clause_one
  have hle := primeRank_le_of_injective 3 L.subtype L.subtype_injective
  exact ComponentReduction.PreliminaryActions.rankOneAction_of_source ρ
    (by omega) c.clause_one

end CFSG.Quasithin.ChapterB.SourceInduction
