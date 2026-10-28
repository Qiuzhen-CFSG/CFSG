module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.DihedralSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SmallEightSource

/-!
# Terminal recognition with the small-Sylow F source discharged

When the original quotient Sylow has order at most eight, the complete source
F family is now proved from A/C and the original SQTK quotient. Applying it to
the actual two local images supplies the same terminal alternatives and embedded
residual identity. Only the independent B-side action classification remains;
there is no F-classification premise in this consumer.
Source: Aschbacher–Smith, F.6.16–18 and the final proof of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u
namespace SourceInput
variable {H : Type u} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

theorem source_intersection_of_sylow_le_eight {K : GroupClass.{u}}
    (hA : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremA K U)
    (hC : ∀ (U : Type u) [Group U] [Finite U], ChapterA.Section02.TheoremC K U)
    (hH : IsSQTK K H) (hcard : Nat.card d.quotientSylow ≤ 8)
    (classificationB : SourceFFClassificationInput.{u,u} K) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H) := by
  have hF := FSource.small_sylow_eight_source hA hC
    (threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core)
    (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt)
    d.quotientSylow d.quotient_intersection hcard
  exact d.source_intersection_of_adequate_classifications hF
    (classificationB _ _ _ (d.offender_hypothesis hH))

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
