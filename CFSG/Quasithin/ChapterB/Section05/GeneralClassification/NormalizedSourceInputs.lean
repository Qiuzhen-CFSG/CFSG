module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInputs
public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.Normalization

/-!
# Adequate B.5 with unconditional component normalization

The genuine B.1.5(4) proof supplies the normalization input to the existing
full-known-simple assembly. The remaining independent source obligations are
B.5.1, A.2, A.3.6 and corrected B.4.2. Every natural-module and outer-action
alternative of the existing adequate classifier is retained.
-/

public section
namespace CFSG.Quasithin.ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v

/-- The full adequate classifier after discharging B.1.5(4) from the original
source hypotheses, preserving the complete known-simple catalogue. -/
theorem adequateClassification_knownSimple_of_classification_theorems
    (h1 : ProjectiveLine.QuasisimpleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple) :
    AdequateClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
  adequateClassification_knownSimple_of_source_theorems h1 hA h36
    PreparationSource.componentNormalization h4
end CFSG.Quasithin.ChapterB.SourceInduction
