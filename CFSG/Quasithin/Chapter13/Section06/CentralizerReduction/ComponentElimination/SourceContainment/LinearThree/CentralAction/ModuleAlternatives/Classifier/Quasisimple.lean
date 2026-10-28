module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.Ranks
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.GroupTheory.PrimeRankZero
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree

/-!
# Extracting the L₃(2) rows from the full B.5.1 conclusion

The actual component isomorphism gives order 168 and three-rank one. The
exhaustive, projective-line-correct B.4.2/B.5.1 rank comparison leaves the
SL₂, SL₃ and marked A₅ rows. Orders exclude SL₂ and A₅. In the remaining
SL₃ rows, the unipotent subgroup has order q³ dividing 168, forcing q = 2.
The existing field transport preserves the matrix action and gives a common
actor isomorphism and intertwiner on both copies in the doubled row.

The output uses the supplied conclusion's literal moved section throughout.
No central-extension splitting is needed for its natural quotient, and no
seed, classification, model-comparison or module witness remains as a premise.
This proves the conditional extraction from the full earlier conclusion;
it does not prove the universal B.5.1 implication.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2,
printed p.86; B.5.1, printed pp.99–103; and the two module alternatives
in the proof of 13.6.20, printed p.931 (PDF p.948).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
open ChapterB.QuasisimpleSource ChapterB.SourceInduction
open ChapterB.QuasisimpleSource.ExtensionConsequences
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions

private theorem three_rank {C : Type*} [Group C] [Finite C] (e : C ≃* Matrix.PSL3Two.PSL) :
    primeRank 3 C = 1 := by
  have hc : Nat.card C = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  let P : Sylow 3 C := Classical.choice inferInstance
  have hp : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hc]
    decide +kernel
  have hu := P.primeRank_le_one_of_isCyclic (isCyclic_of_prime_card hp)
  have hn : primeRank 3 C ≠ 0 := by
    intro hz
    have h := PrimeRank.eq_zero_iff_not_dvd_card.mp hz
    rw [hc] at h
    exact h (by decide)
  omega

private theorem field_degree (F : BinaryField)
    (hc : Nat.card SL(3, F.Carrier) = 168) : F.degree = 1 := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, ← pow_mul, hc] at hd
  have hp := F.degree_pos
  by_contra hn
  have htwo : 2 ≤ F.degree := by omega
  have hdiv : 64 ∣ 168 :=
    (show 2 ^ 6 ∣ 2 ^ (F.degree * 3) from pow_dvd_pow 2 (by omega)).trans hd
  norm_num at hdiv

private theorem no_linearTwo (F : BinaryField) (hc : Nat.card SL(2, F.Carrier) = 168) : False := by
  rw [Atlas.card_sl_two, F.card_eq] at hc
  have hn : F.degree ≤ 2 := by
    by_contra h
    have hh : 8 ≤ 2 ^ F.degree :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ F.degree)
    have hsq : 63 ≤ (2 ^ F.degree) ^ 2 - 1 := by
      have hs : 64 ≤ (2 ^ F.degree) ^ 2 := by nlinarith
      omega
    have hmul := Nat.mul_le_mul hh hsq
    omega
  have hp := F.degree_pos
  interval_cases h : F.degree <;> norm_num [h] at hc

private def compose {D E H V W X : Type*} [Group D] [Group E] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) D V} {σ : Representation (ZMod 2) E W}
    {τ : Representation (ZMod 2) H X}
    (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) : ActionEquiv ρ τ :=
  ⟨e.groupEquiv.trans f.groupEquiv, e.linearEquiv.trans f.linearEquiv,
    fun g v => (congrArg f.linearEquiv (e.intertwines g v)).trans
      (f.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩

variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

/-- Extract the two binary rows on the specified source section. The natural
row retains its literal fixed quotient and commutator generation; the doubled
row uses one actor identification on the moved space itself. -/
theorem quasisimple_rows (e : C ≃* Matrix.PSL3Two.PSL)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) :
    (subspaceCommutator ρ c.sectionData.space.toSubmodule C =
        c.sectionData.space.toSubmodule ∧
      Nonempty (ActionEquiv (c.sectionData.action.comp C.subtype) BinaryLinearThree.W)) ∨
    Nonempty (ActionEquiv (c.sectionData.space.toRepresentation.comp C.subtype)
      (repeated BinaryLinearThree.W 2)) := by
  have hc : Nat.card C = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hr := rankOneAction_of_source ρ (three_rank e) c.clause_one
  cases hr with
  | irreducible hi _ _ source _ =>
    left
    refine ⟨hi.choose_spec.1, ?_⟩
    cases source with
    | linearTwo F _ a _ _ =>
      exact (no_linearTwo F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)).elim
    | linearThree F _ _ a _ =>
      have hF := field_degree F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)
      exact ⟨compose a (degreeOneNaturalEquiv F hF 3)⟩
    | symmetricFive a _ _ =>
      have ha := (Nat.card_congr a.subgroupEquiv.toEquiv).symm.trans hc
      rw [nat_card_alternatingGroup, Nat.card_fin] at ha
      norm_num [Nat.factorial] at ha
  | doubleThree F _ _ a _ _ =>
    right
    have hF := field_degree F ((Nat.card_congr a.groupEquiv.toEquiv).symm.trans hc)
    exact ⟨compose a (degreeOneRepeatedEquiv F hF 3 2)⟩

/-- The complete quasisimple-row extraction contract for the classifier.
All group, field and module comparisons have been discharged. -/
theorem quasisimple_case (e : C ≃* Matrix.PSL3Two.PSL)
    (c : ProjectiveLine.QuasisimpleSourceConclusion ρ C) : LinearThreeModuleCase ρ C := by
  rcases quasisimple_rows e c with h | h
  · exact .natural c.sectionData h.1 (Classical.choice h.2)
  · exact .doubled c.sectionData (Classical.choice h)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier
