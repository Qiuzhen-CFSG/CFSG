module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.CoordinateAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.CyclicCommutant

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.IntrinsicStructure
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.TensorAction

/-!
# Intrinsic algebra of the literal seed centralizer

The literal displacement has rank 56 and equal image and kernel. Its
nondegenerate symmetric Wall form identifies the complete ten-dimensional
radical part of the original exterior space with ten commuting square-zero
operators. Their graded algebra has dimensions 1, 10, 34, 10, 1, is cyclic,
and equals its full endomorphism commutant.

The full ambient seed centralizer acts by inverse pullback on the radical
forms. In the exact certified coordinates, `rho` is a homomorphism to GL(10,2)
and the adjoint action is conjugation by its actual kernel restriction.
The fourfold product defines the alternating form `phi`, proved equal to
`BinaryQuarticMathieu.quartic` with the literal saved coefficient word.
`rhoToQuarticStabilizer` takes values in that tensor's actual stabilizer.
Every element in its kernel has its exact `restrictionBlock` in `algebraSpan`.

All extra coordinate, completeness and multiplication premises are discharged
by the imported certificates. The separate ambient order assembly supplies
cross-module coordinate comparisons and the image and kernel order bounds.
Matrix provenance and conventions are recorded in `IntrinsicAlgebra/source/README.md`.
-/
