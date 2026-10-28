module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases.Models
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Reduction

/-!
# The complete quasisimple rank-one module comparison

The source-correct B.5.1 case reduction at three-rank one leaves the SL₂,
SL₃ and marked A₅ rows, including the doubled SL₃ row. An SL₂ component
cannot be an SL₃ actor because the latter contains an element of order four.
The SL₂ row transports to the supplied field. In the A₅ row, vanishing of
first cohomology for the natural action and its dual splits the moved space
from its fixed kernel; the actual quotient map then supplies its coordinates.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.1(1),(2),
pp.99–103; the first paragraph of 13.6.18, p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
open ChapterB.QuasisimpleSource ChapterB.SourceInduction

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences

/-- Exhaustive B.5.1 specialization for the marked SL₂ component. The
natural row retains its central quotient. The marked A₅ row splits by the
proved odd alternating cohomology theorem, so its coordinates are on the
whole moved space and its original Irr⁺ membership is retained. -/
theorem quasisimple_case [Module.Finite (ZMod 2) V]
    (F : BinaryField) (e : C ≃* SL(2,F.Carrier))
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) : RankOneComponentCase ρ C F := by
  have hr : primeRank 3 C = 1 := by
    have hl : primeRank 3 C ≤ 1 := (primeRank_equiv 3 e).trans_le (three_rank_le F)
    have h3 := Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
      (F := F.Carrier) (i := (0 : Fin 2)) (j := 1) (by decide)
    have hd : 3 ∣ Nat.card SL(2,F.Carrier) :=
      (h3.trans (card_subgroup_dvd_card _)).trans
        (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' (center SL(2,F.Carrier)))
          (QuotientGroup.mk'_surjective _))
    have hp : primeRank 3 C ≠ 0 := by
      rw [primeRank_equiv 3 e]
      exact fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
    omega
  cases rankOneAction_of_source ρ hr c.clause_one with
  | doubleThree E _ _ a _ _ =>
    exact (not_linearThree F E (e.symm.trans a.groupEquiv)).elim
  | irreducible hi _ _ hrow _ =>
    cases hrow with
    | linearTwo E _ a _ _ =>
      exact .natural c.sectionData (FactorExtraction.transAction a
        (sameFieldNatural E F (a.groupEquiv.symm.trans e)))
    | linearThree E _ _ a _ =>
      exact (not_linearThree F E (e.symm.trans a.groupEquiv)).elim
    | symmetricFive a _ _ =>
      have hc := symmetricOdd_isCompl c.sectionData hi (Or.inl rfl) a
      exact .alternatingFive c.sectionData hi
        (FactorExtraction.transAction (FactorExtraction.movedActionOfCentralBot c.sectionData
          (disjoint_iff.mp hc.disjoint)) (markedRestriction a))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.ClassifierCases
end
