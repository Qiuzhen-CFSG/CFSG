module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.DihedralSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.SquareField

/-!
# The actual square-field branch in the terminal intersection

The full B-side action forces the square-field prime to be three for both
source congruences. The retained Frobenius involution then gives the actual
symmetric-six quotient. The original two-group quotient and embedded residual
identity follow from this same extension data, without a local-marking premise.
Source: Aschbacher–Smith, F.6.18 and the final proof of 15.3.1, p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
    [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Both square-field congruences are restricted by the genuine offender
representation, rather than by a local-generator assertion. -/
theorem source_square_field_prime
    (r : FSource.SquareFieldExtensionRow d.quotientSylow)
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion d.offenderAction
      (generalizedFitting d.offenderGroup)) : r.field.prime = 3 := by
  have hm := r.congruence
  apply d.source_square_psl_component_prime r.quasisimple c r.field r.degree
    (Nat.odd_iff.mpr (by omega)) r.componentEquiv
  obtain ⟨es⟩ := r.sylow
  rw [Nat.card_congr es.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
  norm_num [FSource.C]

/-- The actual Frobenius extension is symmetric-six after the independent
B-side source classification restricts its defining prime. -/
theorem source_square_field_symmetricSix
    (r : FSource.SquareFieldExtensionRow d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    Nonempty (coreQuotient H ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨c⟩ := d.source_offender_quasisimple_of_classifications r.quasisimple hB
  have hp := d.source_square_field_prime r c
  exact ComponentRows.OddFields.fieldRow_nine_equiv_symmetricSix
    (r.toFieldExtension hp) hp d.quotientSylow r.sylow.some

/-- All original terminal intersection outputs for the square-field branch. -/
theorem source_square_field_intersection
    (r : FSource.SquareFieldExtensionRow d.quotientSylow)
    (hB : SourceFFAlternative d.offenderAction) :
    NonS3ImageAlternative ((thompsonGroup H).map coreProjection) ∧
      AmbientAlternative (coreQuotient H) ∧
      (pResidual 2 (thompsonGroup H)).map (thompsonGroup H).subtype = pResidual 2 H := by
  obtain ⟨c⟩ := d.source_offender_quasisimple_of_classifications r.quasisimple hB
  have hp := d.source_square_field_prime r c
  obtain ⟨e⟩ := ComponentRows.OddFields.fieldRow_nine_equiv_symmetricSix
    (r.toFieldExtension hp) hp d.quotientSylow r.sylow.some
  have h := d.component_row_symmetricSix r.quasisimple e
  exact ⟨h.1, h.2.1, d.residual_eq_of_fitting_quotient r.quasisimple
    (ComponentRows.fieldRow_quotient (r.toFieldExtension hp))⟩

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
