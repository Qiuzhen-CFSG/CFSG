module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.FullSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedG2Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedMathieuSource

/-!
# The original marked large amalgams in the terminal quotient

Apply the completed derived-G₂ and Mathieu source families to the literal
two-core images, allowing either source orientation. Every component, field,
local extension and residual conclusion is constructed by those families.
The original terminal output therefore follows without a universal F premise.
The genuine earlier marked F.1.12 case and the independent A/C and B-module
theorems remain explicit.

Source: Aschbacher–Smith F.1.12(I)(8,12,13), F.6.18(10,12,13), and 15.3.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open ChapterF.GreenBook
universe u

/-- The three completed large marked families, using the original inclusion maps. -/
def CompletedLargeMarking {D : Type u} [Group D] (A B : Subgroup D) : Prop :=
  let α := RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right
  ExceptionalModels.G2.IsDerivedAmalgam α ∨
    MathieuTwelve.IsM12Amalgam α ∨ AutMathieuTwelve.IsAutM12Amalgam α

private theorem completed_large_source {D : Type u} [Group D] [Finite D]
    {K : GroupClass.{u}} {A B : Subgroup D}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (q : ThreePrimeSQTKQuotient K D) (h : ChapterF.IsGoldschmidtTriple A B)
    (S : Sylow 2 D) (hS : A ⊓ B = (S : Subgroup D))
    (hM : CompletedLargeMarking A B) :
    FSource.SourceAlternative A B S ∨ FSource.SourceAlternative B A S := by
  rcases hM with hM | hM | hM
  · exact FSource.source_of_marked_derived_g2 hA hC q h S hS hM
  · exact FSource.source_of_marked_mathieu hA hC q h S hS hM
  · exact FSource.source_of_marked_aut_mathieu hA hC q h S hS hM

namespace Intersection.SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

omit [IsElementaryAbelian 2 (moduleClosure V)] in
/-- The exact quotient source alternative in either permitted orientation. -/
theorem source_alternative_of_completed_large_marking {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (hM : CompletedLargeMarking (d.G1.map coreProjection) (d.G2.map coreProjection) ∨
      CompletedLargeMarking (d.G2.map coreProjection) (d.G1.map coreProjection)) :
    FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow := by
  let q := threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core
  have h := goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt
  rcases hM with hM | hM
  · exact completed_large_source hA hC q h d.quotientSylow d.quotient_intersection hM
  · exact (completed_large_source hA hC q h.symm d.quotientSylow
      ((inf_comm _ _).trans d.quotient_intersection) hM).symm

/-- Every original non-S₃ field from a completed marked F.1.12 family. -/
theorem source_nonS3_cases_of_completed_large_marking {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (hM : CompletedLargeMarking (d.G1.map coreProjection) (d.G2.map coreProjection) ∨
      CompletedLargeMarking (d.G2.map coreProjection) (d.G1.map coreProjection))
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d :=
  d.source_nonS3_cases_of_source_alternatives
    (d.source_alternative_of_completed_large_marking hA hC hH hM)
    (d.full_sourceFF_alternative hH classificationB) hnot

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
