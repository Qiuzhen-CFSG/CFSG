module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.SquareFieldSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SourceAlternatives

/-!
# Both genuine rank-one source branches in the terminal intersection

Apply the full source interface on the literal O₂ quotient and its original
local images. The ambient dihedral and square-field branches give the same
terminal outputs through their actual offender actions. The universal F and B
classifications remain explicit until their separate source producers close.
Source: Aschbacher–Smith F.6.18 and the final proof of 15.3.1, p.1155.
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

theorem source_intersection_of_source_alternatives
    (hF : FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H) := by
  rcases hF with hF | hF <;> rcases hF with hF | hr
  · exact d.source_intersection_of_adequate_classifications (Or.inl hF) hB
  · exact Or.inr (d.source_square_field_intersection hr.some hB)
  · exact d.source_intersection_of_adequate_classifications (Or.inr hF) hB
  · exact Or.inr (d.source_square_field_intersection hr.some hB)

theorem source_moduleClosure_commutator_of_source_alternatives
    (hF : FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    d.YF ≤ thompsonGroup H ∧ moduleClosure V = ⁅moduleClosure V, thompsonGroup H⁆ := by
  rcases d.source_intersection_of_source_alternatives hF hB with h | ⟨_, _, hres⟩
  · exact (hnot h).elim
  · exact ⟨(d.toActionInput hres).thompson_contains, (d.toActionInput hres).closure_commutator⟩

omit [IsElementaryAbelian 2 (moduleClosure V)] in
theorem source_goldschmidt_alternative {K : GroupClass.{u}} (hH : IsSQTK K H)
    (classification : FSource.SourceClassificationInput K) :
    FSource.SourceAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.SourceAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow := by
  obtain ⟨S, hS, h⟩ := classification (coreQuotient H) _ _
    (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt)
    (threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core)
  have he : S = d.quotientSylow := Sylow.ext (hS.symm.trans d.quotient_intersection)
  exact he ▸ h

include d in
theorem source_intersection_of_source_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.SourceClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H) := by
  exact d.source_intersection_of_source_alternatives
    (d.source_goldschmidt_alternative hH classificationF)
    (classificationB _ _ _ (d.offender_hypothesis hH))

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
