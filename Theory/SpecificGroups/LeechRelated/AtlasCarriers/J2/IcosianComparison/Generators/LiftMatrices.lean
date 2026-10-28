module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.Pair
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.IcosianComparison.Generators.RelatorMatrices

/-!
# Connecting the coefficient certificates to the lattice group

The five reflection matrices are checked directly on the coordinate vectors.
Their products identify the two cover words with the coefficient tables.
The faithful matrix homomorphism then transfers exact identities back to the
unchanged Hermitian lattice stabilizer, including its central negative sign.

The imported root certificates and coordinates retain Gerald Höhn's ATLAS
attribution and license. The literal target words are ATLAS `J2G1-P2`.
-/

set_option Elab.async false

public section
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
open Atlas.Conway Atlas.Algebra Atlas.Lattices RelatorMatrices

local instance : DecidableEq IcosianQuaternion := fun a b =>
  decidable_of_iff (a.re = b.re ∧ a.imI = b.imI ∧ a.imJ = b.imJ ∧ a.imK = b.imK)
    QuaternionAlgebra.ext_iff.symm

private theorem diagonal_one_matrix :
    matrixHom (icosianReflectionDiagonalGenerator 1) = d1 := by
  decide +kernel

private theorem diagonal_two_matrix :
    matrixHom (icosianReflectionDiagonalGenerator 2) = d2 := by
  decide +kernel

private theorem transition_zero_matrix :
    matrixHom (icosianAxisTransitionGenerator 0) = t0 := by
  decide +kernel

private theorem transition_one_matrix :
    matrixHom (icosianAxisTransitionGenerator 1) = t1 := by
  decide +kernel

private theorem transition_three_matrix :
    matrixHom (icosianAxisTransitionGenerator 3) = t3 := by
  decide +kernel

theorem matrixHom_xLift : matrixHom xLift = mx := by
  simp only [xLift, map_mul, transition_one_matrix, diagonal_two_matrix,
    transition_three_matrix, diagonal_one_matrix, x01_mul, x012_mul, x0123_mul]

theorem matrixHom_yLift : matrixHom yLift = my := by
  simp only [yLift, map_mul, diagonal_one_matrix, transition_zero_matrix,
    transition_three_matrix, y01_mul, y012_mul, y0123_mul]

theorem matrixHom_centralSign : matrixHom icosianCentralSign = (-1 : QMatrix) := by
  apply Matrix.ext
  intro i j
  change icosianCentralSign.val (Pi.single j 1) i = _
  rw [icosianCentralSign_apply]
  change -(Pi.single j 1 : IcosianRationalCoordinates) i = -((1 : QMatrix) i j)
  simp [Pi.single_apply, Matrix.one_apply]

/-- Left-inverse matrix data identify the matrix of the actual group inverse. -/
theorem matrixHom_inv_of_mul (g : icosianHermitianGroup) (M : QMatrix)
    (h : M * matrixHom g = 1) : matrixHom g⁻¹ = M := by
  calc
    matrixHom g⁻¹ = 1 * matrixHom g⁻¹ := (one_mul _).symm
    _ = (M * matrixHom g) * matrixHom g⁻¹ := by rw [h]
    _ = M := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem matrixHom_xLift_inv : matrixHom xLift⁻¹ = mxi := by
  apply matrixHom_inv_of_mul
  rw [matrixHom_xLift]
  exact xix_mul

theorem matrixHom_yLift_inv : matrixHom yLift⁻¹ = myi := by
  apply matrixHom_inv_of_mul
  rw [matrixHom_yLift]
  exact yyy_mul

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
