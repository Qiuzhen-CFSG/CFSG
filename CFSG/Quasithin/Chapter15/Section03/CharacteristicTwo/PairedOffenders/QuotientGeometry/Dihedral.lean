module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Center
public import Theory.GroupTheory.SpecificGroups.DihedralEightRecognition

/-!
# The actual dihedral quotient model

The block-kernel quotient has order eight and contains the even elementary
four-group, whose order exceeds that of the center. The proved recognition
of a group of order eight with a noncentral elementary four-group yields an
actual multiplicative equivalence with `DihedralGroup 4`.

Source: Aschbacher–Smith, proof of 15.3.25, printed p.1133.
-/

public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

/-- The actual quotient is dihedral of order eight, not just a group of that order. -/
theorem quotient_dihedral : Nonempty (Quotient ≃* DihedralGroup 4) := by
  apply dihedral_eight_of_noncentral_elementary_four card_quotient evenFour card_evenFour
  intro h
  have hc := Subgroup.card_le_of_le h
  rw [card_evenFour, card_center] at hc
  omega

noncomputable def dihedralEquiv : Quotient ≃* DihedralGroup 4 :=
  Classical.choice quotient_dihedral

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
