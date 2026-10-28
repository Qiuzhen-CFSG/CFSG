module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.DihedralPSL2

/-!
# Terminal comparison with the ambient dihedral PSL₂ source branch

The actual offender action restricts the ambient PSL₂ field without any local
S₄ assertion. Combining this calculation with the existing thirteen-row
comparison proves the same terminal alternatives, residual identity and module
commutator statement from the adequate source interface. The quotient maps and
both original local factors are unchanged.

Source: Aschbacher–Smith, F.6.18, printed pp.309–310, and the final proof of
15.3.1, printed p.1155. The universal F and B inputs still require their source
producers; this module proves their application to the original configuration.
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

/-- The source PSL₂ branch yields the exact embedded residual identity from
its genuine B-side action, without a local-group isomorphism premise. -/
theorem source_dihedral_psl_intersection
    (r : FSource.DihedralPSL2Row d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H := by
  obtain ⟨c⟩ := d.source_offender_quasisimple_of_classifications r.quasisimple hB
  obtain ⟨hX, hD, hquot⟩ := d.source_component_dihedral_pslTwo r.quasisimple c
    r.field r.degree r.congruence r.model r.component r.sylow
  exact ⟨hX, hD, d.residual_eq_of_fitting_quotient r.quasisimple hquot⟩

/-- The adequate source alternatives give the same terminal intersection
on the literal Thompson image and the actual offender action. -/
theorem source_intersection_of_adequate_classifications
    (hF : FSource.AdequateAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.AdequateAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H) := by
  rcases hF with hF | hF <;> rcases hF with hF | hr
  · exact d.source_intersection_of_classifications (Or.inl hF) hB
  · obtain ⟨r⟩ := hr
    exact Or.inr (d.source_dihedral_psl_intersection r hB)
  · exact d.source_intersection_of_classifications (Or.inr hF) hB
  · obtain ⟨r⟩ := hr
    exact Or.inr (d.source_dihedral_psl_intersection r hB)

/-- The same source application supplies the module-generation premise of
later action recognition after the separate symmetric-three exclusion. -/
theorem source_moduleClosure_commutator_of_adequate_classifications
    (hF : FSource.AdequateAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.AdequateAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction)
    (hnot : ¬ Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3))) :
    d.YF ≤ thompsonGroup H ∧ moduleClosure V = ⁅moduleClosure V, thompsonGroup H⁆ := by
  rcases d.source_intersection_of_adequate_classifications hF hB with h | ⟨_, _, hres⟩
  · exact (hnot h).elim
  · exact ⟨(d.toActionInput hres).thompson_contains, (d.toActionInput hres).closure_commutator⟩

omit [IsElementaryAbelian 2 (moduleClosure V)] in
/-- The actual O₂ quotient is an O₃′ quotient by the source core equality,
and its local images retain their prescribed common Sylow. -/
theorem adequate_goldschmidt_alternative {K : GroupClass.{u}} (hH : IsSQTK K H)
    (classification : FSource.AdequateClassificationInput K) :
    FSource.AdequateAlternative (d.G1.map coreProjection) (d.G2.map coreProjection)
        d.quotientSylow ∨
      FSource.AdequateAlternative (d.G2.map coreProjection) (d.G1.map coreProjection)
        d.quotientSylow := by
  obtain ⟨S, hS, h⟩ := classification (coreQuotient H) _ _
    (goldschmidt_twoCore_quotient d.G1 d.G2 d.goldschmidt)
    (threePrimeSQTKQuotient_of_core_eq hH d.three_prime_core)
  have he : S = d.quotientSylow := Sylow.ext (hS.symm.trans d.quotient_intersection)
  exact he ▸ h

include d in
/-- Apply both universal source inputs to the genuine 15.3.66–68 data.
The adequate F input retains the ambient dihedral PSL₂ branch; the full B
input retains its representation on the original offender actor. -/
theorem source_intersection_of_full_adequate_classifications {K : GroupClass.{u}}
    (hH : IsSQTK K H)
    (classificationF : FSource.AdequateClassificationInput K)
    (classificationB : SourceFFClassificationInput.{u,u} K) :
    Nonempty ((thompsonGroup H).map coreProjection ≃* Equiv.Perm (Fin 3)) ∨
      (NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
        AmbientAlternative (coreQuotient H) ∧
        (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H) := by
  exact d.source_intersection_of_adequate_classifications
    (d.adequate_goldschmidt_alternative hH classificationF)
    (classificationB _ _ _ (d.offender_hypothesis hH))

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
