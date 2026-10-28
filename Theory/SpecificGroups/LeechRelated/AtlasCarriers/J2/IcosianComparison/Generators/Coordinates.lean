module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionDiagonal
/-!
# Faithful quaternion matrices for the lattice pair

A right quaternion-linear map is determined on the three coordinate vectors.
Evaluation on these vectors gives a faithful matrix homomorphism, retaining
left multiplication and the usual composition convention. This lets small
exact coefficient certificates establish identities in the actual lattice
isometry group. The right-linearity input is part of the existing Hermitian
stabilizer definition, from Gerald Höhn's icosian construction.
-/

@[expose] public section

open Atlas.Conway Atlas.Algebra Atlas.Lattices
open scoped BigOperators
namespace Sporadic.LeechRelated.J2.IcosianComparison.Generators
noncomputable def matrix (g : icosianHermitianGroup) : Matrix (Fin 3) (Fin 3) IcosianQuaternion :=
  fun i j => g.val (Pi.single j 1) i

theorem apply_eq_matrix (g : icosianHermitianGroup) (v : IcosianRationalCoordinates) :
    g.val v = (matrix g).mulVec v := by
  have hv : v = icosianRightMul (Pi.single 0 1) (v 0) +
      icosianRightMul (Pi.single 1 1) (v 1) +
      icosianRightMul (Pi.single 2 1) (v 2) := by
    funext i
    fin_cases i <;> simp [icosianRightMul]
  conv_lhs => rw [hv, map_add, map_add, g.property.1, g.property.1, g.property.1]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, matrix, icosianRightMul, add_assoc]

noncomputable def matrixHom : icosianHermitianGroup →*
    Matrix (Fin 3) (Fin 3) IcosianQuaternion where
  toFun := matrix
  map_one' := by
    apply Matrix.ext
    intro i j
    change (Pi.single j 1 : IcosianRationalCoordinates) i = _
    simp [Matrix.one_apply, Pi.single_apply]
  map_mul' g h := by
    apply Matrix.ext
    intro i j
    change g.val (h.val (Pi.single j 1)) i = _
    rw [apply_eq_matrix]
    rfl

theorem matrixHom_injective : Function.Injective matrixHom := by
  intro g h he
  apply Subtype.ext
  apply icosian_right_linear_ext _ _ g.property.1 h.property.1
  intro j
  funext i
  exact congrFun (congrFun he i) j

end Sporadic.LeechRelated.J2.IcosianComparison.Generators
