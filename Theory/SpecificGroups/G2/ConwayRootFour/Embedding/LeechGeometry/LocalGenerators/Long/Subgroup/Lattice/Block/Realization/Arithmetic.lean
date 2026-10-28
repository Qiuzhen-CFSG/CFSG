module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.LatticeData

/-!
# Integer certificates for the glued lattice action

Clearing denominators checks the basis inverse and the two generator actions
using integer products. The rational form identities are deduced structurally
from the six-dimensional Hermitian identities in the consumer `Lattice`.
This avoids repeatedly reducing dense rational products in the kernel.

The original matrices are John Bray's ATLAS `6L34G1-Ar6aB0`; the derived
coordinate tables and their reproducible construction are in `LatticeData`.
-/

@[expose] public section
open Matrix Atlas.Algebra
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

theorem basis_mul_inverse_integer : basisNumerator * basisInverse = 2 := by
  decide +kernel

theorem numeratorA : realification matrixA.conjTranspose =
    (1/2 : ℚ) • integerMatrix actionANumerator := by decide +kernel

theorem numeratorB : realification matrixBInv.conjTranspose =
    (1/2 : ℚ) • integerMatrix actionBNumerator := by decide +kernel

theorem numeratorBInverse : realification matrixB.conjTranspose =
    (1/2 : ℚ) • integerMatrix actionBInverseNumerator := by decide +kernel

theorem integerA : actionANumerator * basisNumerator =
    2 • (basisNumerator * generatorACoordinates) := by decide +kernel

theorem integerB : actionBNumerator * basisNumerator =
    2 • (basisNumerator * generatorBCoordinates) := by decide +kernel

theorem integerBInverse : actionBInverseNumerator * basisNumerator =
    2 • (basisNumerator * generatorBInverseCoordinates) := by decide +kernel

theorem matrixBInv_form : matrixBInv * hermitianMatrix * matrixBInv.conjTranspose =
    hermitianMatrix := by decide +kernel

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
