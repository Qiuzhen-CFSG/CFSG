module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.FullSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CharacteristicTwoReduction

/-!
# The remaining characteristic-two source branch in the terminal quotient

Apply the complete exceptional-vertex source theorem to the original two
local images. All terminal outputs follow without an F-classification premise.
The final reduction retains exactly the remaining characteristic-two source
pair in the same quotient, with its actual Sylow and quasisimple residual.
The independent A/C and B-module source theorems remain explicit.

Source: Aschbacher–Smith F.6.5, F.6.18 and the final proof of 15.3.1, p.1155.
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

/-- Every exceptional-vertex terminal case has all original outputs. -/
theorem source_nonS3_cases_of_exceptional_vertex {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (hbad : generalizedFitting (d.G1.map coreProjection) ≠ pCore 2 (d.G1.map coreProjection) ∨
      generalizedFitting (d.G2.map coreProjection) ≠ pCore 2 (d.G2.map coreProjection))
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d := by
  have hF := FSource.exceptional_vertex_source hA hC
    (threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core)
    (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt)
    d.quotientSylow d.quotient_intersection hbad
  exact d.source_nonS3_cases_of_source_alternatives hF
    (d.full_sourceFF_alternative hH classificationB) hnot

/-- All terminal cases except the precise remaining marked F.1.12 branch
are discharged, preserving the actual quotient and original vertices. -/
theorem source_nonS3_cases_or_characteristic_two {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d ∨
      (8 < Nat.card d.quotientSylow ∧
        pResidual 2 (coreQuotient H) = generalizedFitting (coreQuotient H) ∧
        IsQuasisimple (pResidual 2 (coreQuotient H)) ∧
        generalizedFitting (d.G1.map coreProjection) = pCore 2 (d.G1.map coreProjection) ∧
        generalizedFitting (d.G2.map coreProjection) = pCore 2 (d.G2.map coreProjection) ∧
        ¬ Nonempty (d.quotientSylow ≃* (FSource.C 2 × DihedralGroup 4))) := by
  obtain ⟨S,hS,ha⟩ := FSource.source_alternative_or_characteristic_two hA hC
    (threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core)
    (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt)
  have he : S = d.quotientSylow := Sylow.ext (hS.symm.trans d.quotient_intersection)
  subst S
  rcases ha with ha | ha
  · exact Or.inl (d.source_nonS3_cases_of_source_alternatives ha
      (d.full_sourceFF_alternative hH classificationB) hnot)
  · exact Or.inr ha

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
