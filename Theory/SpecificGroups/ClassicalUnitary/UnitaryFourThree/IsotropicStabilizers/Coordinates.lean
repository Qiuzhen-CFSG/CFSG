module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers.ScalarKernel

/-!
# Coordinate stabilizers for the field-nine unitary four-space

The antidiagonal Hermitian matrix pairs the first and fourth coordinates, and
the second and third. Its first coordinate line and first two-coordinate plane
are totally isotropic. Their full SU stabilizers are those already defined in
`UnitaryFourFlag`; here we name their actual images in PGL over Nine.

These shared concrete groups separate the arbitrary-subspace transport problem
from the two coordinate stabilizer calculations. No assertion about the
structure of either stabilizer is assumed. Source: GLS3, chapter 2, classical
unitary spaces; the reducible-subgroup contribution to Aschbacher–Smith,
Theorem 0.1.2(4), condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
-/

open BenderSuzuki.MatrixGroups

public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers

/-- The hyperbolic antidiagonal form, with the same cube conjugation as the identity model. -/
@[expose] def coordinateForm : HermitianForm 4 FiniteField.Nine :=
  UnitaryFourFlag.form FiniteField.Nine conjugation star_involutive

theorem coordinateForm_conj_cube (x : FiniteField.Nine) :
    coordinateForm.conj x = x ^ 3 := FiniteField.Nine.star_eq_cube x

/-- The actual projective image for the coordinate form. -/
abbrev CoordinateCarrier := ProjectiveSpecialUnitaryMatrixGroup coordinateForm

/-- The full stabilizer of the first coordinate line, retaining the scalar quotient. -/
@[expose] def coordinatePointStabilizer : Subgroup CoordinateCarrier :=
  (UnitaryFourFlag.pointParabolicSU FiniteField.Nine coordinateForm).map
    (UnitaryFourFlag.project FiniteField.Nine coordinateForm)

/-- The full stabilizer of the first two-coordinate plane, retaining the scalar quotient. -/
@[expose] def coordinatePlaneStabilizer : Subgroup CoordinateCarrier :=
  (UnitaryFourFlag.planeParabolicSU FiniteField.Nine coordinateForm).map
    (UnitaryFourFlag.project FiniteField.Nine coordinateForm)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
