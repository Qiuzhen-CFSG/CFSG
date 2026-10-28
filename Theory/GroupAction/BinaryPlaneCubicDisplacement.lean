module
public import Theory.GroupAction.BinaryWreathPointStabilizer

/-!
# Cubic displacements on the binary plane

For any nonidentity vector, two displacements by matrices of exponent dividing
three generate every vector of the plane. The kernel check enumerates only
six matrices and four vectors. Surjective maps on two-residuals lift these
matrices to the original group in the orthogonal source application.

Source application: Aschbacher--Smith 14.6.17(5), printed p.1036.
-/


public section
namespace BinaryWreathPointStabilizer
attribute [local instance] FourGroupMatrixCoordinates.naturalAction

/-- Two displacements by cubic matrices generate the binary plane from any
nonzero vector. Only the six matrices and four vectors are enumerated. -/
theorem plane_cubic_displacements : ∀ v : Plane, v ≠ 1 → ∀ w : Plane,
    ∃ m n : MatrixActor, m^3=1 ∧ n^3=1 ∧
      w = (v*(m•v)⁻¹)*(v*(n•v)⁻¹) := by
  decide +kernel

end BinaryWreathPointStabilizer
