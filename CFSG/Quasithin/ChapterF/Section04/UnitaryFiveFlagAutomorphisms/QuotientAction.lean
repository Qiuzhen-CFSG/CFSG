module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.ResidualAction
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Source
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.FieldTheory.BinaryTorusTwoPower

/-!
# The literal PSL₂(16) coefficient of a U₅(4) flag automorphism

Use the embedded solvable residual of the plane parabolic and its canonical
two-core. Its established quotient marking gives a homomorphic field
coefficient. An involution with nonidentity coefficient has exactly the
Hermitian conjugation coefficient. This is the quotient restriction in
F.4.29(2), printed p.289 of refs/quasithin.pdf; full actor representation
requires the additional radical and opposite-endpoint rigidity argument.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup Theory.SpecificGroups.ClassicalUnitary
open GreenBook.UnitaryFive
variable (U : Model 4)

abbrev flagAutomorphisms := NativeAmalgamActions.flagAutomorphisms
  U.leftParabolic U.rightParabolic

def rightLocalAction : flagAutomorphisms U →* MulAut U.rightLocalImage :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightImageAction U.leftParabolic U.rightParabolic

@[simp] theorem rightLocalAction_val (a : flagAutomorphisms U) (x : U.rightLocalImage) :
    (rightLocalAction U a x).val = a.val x.val :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightImageAction_val _ _ a x

theorem rightLocalImage_preserved (a : flagAutomorphisms U) :
    U.rightLocalImage.map a.val.toMonoidHom = U.rightLocalImage :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightResidualImage_preserved _ _ a

def rightQuotientAction : flagAutomorphisms U →*
    MulAut (U.rightLocalImage ⧸ pCore 2 U.rightLocalImage) :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction U.leftParabolic U.rightParabolic

@[simp] theorem rightQuotientAction_mk (a : flagAutomorphisms U) (x : U.rightLocalImage) :
    rightQuotientAction U a (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (rightLocalAction U a x) :=
  Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction_mk _ _ a x

/-- The action in the established residual PSL₂ coordinates. -/
def rightLinearAction : flagAutomorphisms U →* MulAut (Theory.PSL2.Group U.F) :=
  (MulAut.congr U.rightLocalImageQuotientEquiv).toMonoidHom.comp (rightQuotientAction U)

/-- The field factor of the actual residual quotient action. -/
def rightCoefficient : flagAutomorphisms U →* (U.F ≃+* U.F) :=
  (Theory.PSL2.fieldProjection U.F).comp (rightLinearAction U)

/-- Nonidentity and the involution equation determine the exact coefficient. -/
theorem rightCoefficient_eq_conj (a : flagAutomorphisms U) (ha : a ^ 2 = 1)
    (hc : rightCoefficient U a ≠ 1) : rightCoefficient U a = U.form.conj := by
  have hs : (rightCoefficient U a) ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨m,_,hm,hformula⟩ := FiniteField.BinaryTorusTwoPower.involution_eq_half_frobenius
    (show Nat.card U.F = 2 ^ 4 from U.local_field_card) (rightCoefficient U a) hs hc
  have hm2 : m = 2 := by omega
  ext x
  rw [U.conjugation]
  have hh := hformula x
  rw [hm2] at hh
  norm_num only at hh
  exact hh

end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
