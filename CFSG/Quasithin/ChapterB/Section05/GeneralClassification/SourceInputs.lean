module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.ModuleCalculation.NaturalReduction.ModelComparison.BinaryG2Exclusion.TernaryKernel
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.SourceApplications
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.ChiefFactorBound
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.GeneralClassification
public import CFSG.Quasithin.ChapterA.Section01.SectionRank.CyclicCentralizers
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.ComponentLifting
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Discharging the established source inputs of adequate B.5

The full known-simple classification is reduced to genuine B.5.1, A.2,
A.3.6, B.1.5(4) and corrected B.4.2 source implications. All three required
B.4.8 theorems, B.1.9 and A.1.31(1) are proved and supplied here. A.3.6
constructs the actual B.5.2 component cover, and the complete B.5.5 preparation
uses the original SQTK quotient, selected offender and chief section.

The existing direct induction preserves the trivial actor and every adequate
module, outer-action, two-factor and hyperplane alternative. This assembly
has no multiplier-table or binary-G₂ kernel premise. It remains conditional
on its five explicitly named earlier-source theorems; their full proofs are
independent obligations before the unconditional classifier is available.

Source: Aschbacher–Smith B.5.2–12, printed pp.103–110; B.4.8, p.91;
B.1.9, pp.71–72; A.1.31(1), pp.27–28 (1 March 2004 manuscript).
-/

public section

namespace CFSG.Quasithin.ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v

/-- Source A.1.31(1), with its explicit primality argument installed as an instance. -/
theorem earlierA131One : FactorExtraction.EarlierA131One.{u} := by
  intro G _ _ p hp ho hr N _ hF T hT hne
  let : Fact p.Prime := ⟨hp⟩
  exact ChapterA.lemma_A_1_31_1 hr ho hF T hT hne

/-- All proved B.4.8, B.1.9 and A.1.31 inputs are supplied, and the actual
B.5.2/B.5.5 cover and component constructors are applied. The remaining inputs
are precisely the independent earlier classification and normalization theorems. -/
theorem adequateClassification_knownSimple_of_source_theorems
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (hn : PreparationSource.ComponentNormalizationInput.{u,v})
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple) :
    AdequateClassificationInput.{u,v} KnownSimple.IsKnownSimple := by
  exact PreciseMultiplierInputs.adequateClassification_of_source_local_kernel h1
    (coverInput_of_a36 h36) hA (PreparationSource.componentInput hn hA h36 h4) h36
    NaturalExtensions.earlierB48Two FittingStructure.earlierB19 earlierA131One
    NaturalExtensions.earlierB48Three NaturalExtensions.ChiefFactorBound.earlierB48Four
end CFSG.Quasithin.ChapterB.SourceInduction
