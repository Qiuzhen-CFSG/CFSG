module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.CompleteSourceInputs
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete

/-!
# B.5 over the complete known-simple catalogue

The genuine unconditional Theorems A and C now supply both semisimple-section
input and the full A.3.6 covering input. The earlier completed B.5 source
induction therefore retains only the original corrected B.4.2 theorem.
All quasisimple, reducible, cohomological and outer module alternatives of the
adequate target remain unchanged. Source: Aschbacher--Smith B.5.1--12.
-/

public section
namespace CFSG.Quasithin.ChapterB.SourceInduction
universe u v

/-- All known-simple source premises before B.4.2 are discharged. -/
theorem adequateClassification_knownSimple_of_b4
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple) :
    AdequateClassificationInput.{u,v} KnownSimple.IsKnownSimple :=
  adequateClassification_knownSimple_of_earlier_classification
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) h4

end CFSG.Quasithin.ChapterB.SourceInduction
