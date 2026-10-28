module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.FullSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SplitSixteenSource

/-!
# Terminal cases with the split-sixteen F source discharged

The complete split-sixteen theorem applies to the literal images of the two
original vertices under the two-core projection. It supplies the corrected
source alternative and hence every field of the unchanged terminal conclusion.
The genuine earlier A/C and independent B-module classification inputs remain;
there is no F-classification or component-recognition input.

Source: Aschbacher–Smith F.6.18(8–9) and the final proof of 15.3.1, p.1155.
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

omit [IsElementaryAbelian 2 (moduleClosure V)] in
/-- The source alternative on the original quotient Sylow and local images. -/
theorem source_alternative_of_split_sixteen {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (eS : d.quotientSylow ≃* (FSource.C 2 × DihedralGroup 4)) :
    FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow :=
  FSource.split_sixteen_source hA hC
    (threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core)
    (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt)
    d.quotientSylow d.quotient_intersection eS

/-- Every original non-S₃ conclusion follows with the F premise discharged. -/
theorem source_nonS3_cases_of_split_sixteen {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (eS : d.quotientSylow ≃* (FSource.C 2 × DihedralGroup 4))
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    Cases.NonS3Conclusion d :=
  d.source_nonS3_cases_of_source_alternatives
    (d.source_alternative_of_split_sixteen hA hC hH eS)
    (d.full_sourceFF_alternative hH classificationB) hnot

/-- Both original terminal cases, retaining the selected E, Z and span. -/
theorem source_terminal_cases_of_split_sixteen {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H)
    (eS : d.quotientSylow ≃* (FSource.C 2 × DihedralGroup 4))
    (classificationB : SourceFFClassificationInput.{u,u} K)
    (E Z : Subgroup H) (hZE : Z ≤ E)
    (hXE : d.XE ≤ centralizer (E : Set H))
    (hZT : Z ≤ centralizer (d.T : Set H))
    (hFspan : d.F = conjugateSpanBy Z d.YF) :
    Cases.SymmetricThreeConclusion d Z ∨ Cases.NonS3Conclusion d :=
  d.source_terminal_cases_of_source_alternatives E Z hZE hXE hZT hFspan
    (d.source_alternative_of_split_sixteen hA hC hH eS)
    (d.full_sourceFF_alternative hH classificationB)

end Intersection.SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition
