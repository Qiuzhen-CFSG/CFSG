module
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.FormTransport
public import Theory.SpecificGroups.SU3.ProjectiveEntrywiseAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Natural unitary coordinates through Hermitian basis change

The same invertible matrix transports the special unitary action and its
projective image. The scalar projection commutes with this transport, and
multiplication by the basis matrix intertwines the natural binary modules.
This lets a split-quotient profile use its original Hermitian form, including
the binary case with nontrivial scalar kernel.

Source: Huppert, Endliche Gruppen I, II.10.4(b); Fong--Seitz I (6A)(c)
and II (8.13)--(8.15). The original profile application is in
CFSG/Quasithin/ChapterF/Section01/SourceRecognition/FongSeitzBinary/UnitaryFormProfile.
-/

public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFormTransport
open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
variable {E : Type*} [Field E] [CharP E 2]
local instance : Algebra (ZMod 2) E := ZMod.algebra E 2

/-- The basis matrix on the natural module, restricted to binary scalars. -/
def basisCoordinates (C : GL (Fin 3) E) :
    (Fin 3 → E) ≃ₗ[ZMod 2] (Fin 3 → E) :=
  (GeneralLinearGroup.toLin C).toLinearEquiv.restrictScalars (ZMod 2)

@[simp] theorem basisCoordinates_apply (C : GL (Fin 3) E) (v : Fin 3 → E) :
    basisCoordinates C v = C.val *ᵥ v := by rfl

variable (J : HermitianForm 3 E) (C : GL (Fin 3) E)
  (hC : J.conjTranspose C.val * J.form * C.val = (standardForm J).form)

omit [CharP E 2] in
/-- The actual scalar projection is preserved by the same basis change. -/
theorem projective_symm_square (A : (standardForm J).specialSubgroup) :
    (projectiveEquiv J C hC).symm ((standardForm J).specialToProjective A) =
      J.specialToProjective ((specialEquiv J C hC).symm A) := by
  apply Subtype.ext
  simp only [projectiveEquiv_symm_apply, HermitianForm.specialToProjective_apply_val,
    specialEquiv_symm_apply, map_mul, map_inv]

/-- The transported natural action uses the original special-unitary matrices. -/
theorem basisCoordinates_action (A : (standardForm J).specialSubgroup) (v : Fin 3 → E) :
    basisCoordinates C (A.val.val *ᵥ v) =
      ((specialEquiv J C hC).symm A).val.val *ᵥ basisCoordinates C v := by
  rw [basisCoordinates_apply, basisCoordinates_apply, specialEquiv_symm_apply]
  rw [mulVec_mulVec, mulVec_mulVec]
  congr 1
  change (C * A.val).val = (C * A.val * C⁻¹ * C).val
  simp only [mul_assoc, inv_mul_cancel, mul_one]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFormTransport
