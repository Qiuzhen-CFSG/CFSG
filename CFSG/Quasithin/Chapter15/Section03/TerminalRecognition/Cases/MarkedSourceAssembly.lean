module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.FullSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedSourceAssembly

/-!
# Terminal recognition after the remaining marked F.6.5 enumeration

The source assembly constructs the full F classifier from actual A/C and
the precise earlier marked-amalgam implication. Apply it to the original
two-core quotient, preserving all fields of the existing terminal conclusion.
The independent B-module theorem and the original S₃ centralizer/span inputs
retain their existing boundaries.

Source: Aschbacher–Smith F.6.18 and the final proof of 15.3.1, pp.310,1155.
The remaining marked F.6.5 enumeration is explicit and is not asserted here.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
namespace Intersection.SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- All unchanged non-S₃ outputs after the genuine marked source enumeration. -/
theorem source_nonS3_cases_of_characteristic_two_marked_amalgams {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hF1 : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u})
    (hH : IsSQTK K H) (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d :=
  d.source_nonS3_cases_of_source_classifications hH
    (FSource.sourceClassificationInput_of_characteristic_two_marked_amalgams hA hC hF1)
    classificationB hnot

/-- The entire original terminal case split after the same source enumeration. -/
theorem source_terminal_cases_of_characteristic_two_marked_amalgams {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hF1 : ChapterF.SourceAssembly.CharacteristicTwoMarkedAmalgamInput.{u})
    (hH : IsSQTK K H) (classificationB : SourceFFClassificationInput.{u,u} K)
    (E Z : Subgroup H) (hZE : Z ≤ E)
    (hXE : d.XE ≤ centralizer (E : Set H))
    (hZT : Z ≤ centralizer (d.T : Set H))
    (hFspan : d.F = conjugateSpanBy Z d.YF) :
    Cases.SymmetricThreeConclusion d Z ∨ Cases.NonS3Conclusion d :=
  d.source_terminal_cases_of_source_classifications hH
    (FSource.sourceClassificationInput_of_characteristic_two_marked_amalgams hA hC hF1)
    classificationB E Z hZE hXE hZT hFspan

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
