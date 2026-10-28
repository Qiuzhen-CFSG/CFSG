module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedLargeSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.MarkedFullG2Source

/-!
# The full binary G₂ source branch in the original terminal quotient

Apply the completed full G₂ family to the literal two-core images and their
original common Sylow. The source marking may have either orientation. Together
with the three earlier large families this constructs every terminal output
for all four exceptional marked amalgams, without a universal F premise.
The genuine marked F.1.12 enumeration and independent A/C and B-module source
theorems retain their original assembly boundaries.

Source: Aschbacher–Smith F.1.12(I)(3,8,12,13), F.6.18(10–13), and 15.3.1.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open ChapterF.GreenBook
universe u

/-- All four exceptional marked source families, on the original inclusions. -/
def CompletedExceptionalMarking {D : Type u} [Group D] (A B : Subgroup D) : Prop :=
  CompletedLargeMarking A B ∨ ExceptionalModels.G2.IsFullAmalgam
    (RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right)

namespace Intersection.SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

omit [IsElementaryAbelian 2 (moduleClosure V)] in
/-- The exact full G₂ alternative in the original two-core quotient. -/
theorem source_alternative_of_marked_full_g2 {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (hM : ExceptionalModels.G2.IsFullAmalgam
        (RankTwoAmalgam.ofSubgroups (d.G1.map coreProjection)
          (d.G1.map coreProjection ⊓ d.G2.map coreProjection)
          (d.G2.map coreProjection) inf_le_left inf_le_right) ∨
      ExceptionalModels.G2.IsFullAmalgam
        (RankTwoAmalgam.ofSubgroups (d.G2.map coreProjection)
          (d.G2.map coreProjection ⊓ d.G1.map coreProjection)
          (d.G1.map coreProjection) inf_le_left inf_le_right)) :
    FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow := by
  let q := threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core
  have h := goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt
  rcases hM with hM | hM
  · exact FSource.source_of_marked_full_g2 hA hC q h
      d.quotientSylow d.quotient_intersection hM
  · exact (FSource.source_of_marked_full_g2 hA hC q h.symm
      d.quotientSylow ((inf_comm _ _).trans d.quotient_intersection) hM).symm

omit [IsElementaryAbelian 2 (moduleClosure V)] in
/-- Every exceptional marked family supplies the literal source alternative. -/
theorem source_alternative_of_completed_exceptional_marking {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (hM : CompletedExceptionalMarking (d.G1.map coreProjection) (d.G2.map coreProjection) ∨
      CompletedExceptionalMarking (d.G2.map coreProjection) (d.G1.map coreProjection)) :
    FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow := by
  rcases hM with (hM | hM) | (hM | hM)
  · exact d.source_alternative_of_completed_large_marking hA hC hH (Or.inl hM)
  · exact d.source_alternative_of_marked_full_g2 hA hC hH (Or.inl hM)
  · exact d.source_alternative_of_completed_large_marking hA hC hH (Or.inr hM)
  · exact d.source_alternative_of_marked_full_g2 hA hC hH (Or.inr hM)

/-- All unchanged non-S₃ outputs for the four exceptional marked families. -/
theorem source_nonS3_cases_of_completed_exceptional_marking {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (hM : CompletedExceptionalMarking (d.G1.map coreProjection) (d.G2.map coreProjection) ∨
      CompletedExceptionalMarking (d.G2.map coreProjection) (d.G1.map coreProjection))
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d :=
  d.source_nonS3_cases_of_source_alternatives
    (d.source_alternative_of_completed_exceptional_marking hA hC hH hM)
    (d.full_sourceFF_alternative hH classificationB) hnot

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
