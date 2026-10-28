module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Basis

/-!
# Faithful coordinates for the literal max4 subgroup

The supplied inverse identities make conjugation by the displayed basis a
faithful representation of the actual max4 subgroup. The word-evaluation
checks for the eleven normal-closure words remain separate.

Source application: Aschbacher–Smith, condition E, printed pp.3–4 and
481–482. The literal ATLAS program is retained beside `SymmetricLinear.Model`;
the data provenance is in `CharacteristicTwo/source/README.md`.
-/

@[expose] public section

namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
open Coordinates

/-- The proposed coordinate expression; no invertibility is built into it. -/
def coordinates (g : max4Subgroup) : BinaryMatrix :=
  decodeRows basisRows * toMatrix (g : Model) * decodeRows basisInverseRows

/-- The actual change of basis, once its two inverse identities are supplied. -/
def basisUnit
    (hr : decodeRows basisRows * decodeRows basisInverseRows = 1)
    (hl : decodeRows basisInverseRows * decodeRows basisRows = 1) : BinaryMatrixˣ where
  val := decodeRows basisRows
  inv := decodeRows basisInverseRows
  val_inv := hr
  inv_val := hl

/-- Conjugation by the actual basis unit gives a matrix homomorphism on max4. -/
def coordinateHom
    (hr : decodeRows basisRows * decodeRows basisInverseRows = 1)
    (hl : decodeRows basisInverseRows * decodeRows basisRows = 1) :
    max4Subgroup →* BinaryMatrix :=
  (Units.coeHom BinaryMatrix).comp
    ((MulAut.conj (basisUnit hr hl)).toMonoidHom.comp
      (toAmbient.comp max4Subgroup.subtype))

theorem coordinateHom_apply
    (hr : decodeRows basisRows * decodeRows basisInverseRows = 1)
    (hl : decodeRows basisInverseRows * decodeRows basisRows = 1)
    (g : max4Subgroup) : coordinateHom hr hl g = coordinates g := by
  simp only [coordinateHom, MonoidHom.comp_apply, Units.coeHom_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Units.val_mul]
  rfl

theorem coordinateHom_injective
    (hr : decodeRows basisRows * decodeRows basisInverseRows = 1)
    (hl : decodeRows basisInverseRows * decodeRows basisRows = 1) :
    Function.Injective (coordinateHom hr hl) :=
  Units.val_injective.comp ((MulAut.conj (basisUnit hr hl)).injective.comp
    (toAmbient_injective.comp Subtype.val_injective))

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
