module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Realization
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions.Data
public import Theory.Representation.MathieuCodeRestriction.Actions
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Independent inputs for the fifth-exterior-power construction

The first input identifies coordinates of the genuine fifth exterior power of
native M24's eleven-dimensional code. The second consists of seven finite
matrix identities: a surjective quotient onto the 220a matrices and a change
of coordinates from its contragredient to the 220b matrices. Neither input
assumes an action on 220 coordinates, a presentation, or irreducibility.

The candidate quotient and change of basis are saved in `source/quotient.json`.
The assembly in `NativeActions` constructs the actual quotient action and its
dual once these independent inputs have been proved.

Source context: James, J. Algebra 27 (1973), 57--111; GM02 Proposition 5.1.
-/

@[expose] public noncomputable section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions
open Sporadic.Mathieu

/-- Functorial action on the actual fifth exterior power of the native code. -/
def exteriorRepresentation : Representation (ZMod 2) M24 (⋀[ZMod 2]^5 MathieuCode.Code) where
  toFun g := exteriorPower.map 5 (MathieuCode.codeRepresentation g)
  map_one' := by
    rw [map_one]
    exact exteriorPower.map_id
  map_mul' g h := by
    rw [map_mul]
    exact exteriorPower.map_comp (MathieuCode.codeRepresentation h) (MathieuCode.codeRepresentation g)

/-- Native coordinates in the lexicographically ordered five-subset basis. -/
structure ExteriorCoordinates where
  equiv : (⋀[ZMod 2]^5 MathieuCode.Code) ≃ₗ[ZMod 2] (Fin 462 → ZMod 2)
  first : LinearMap.toMatrix' (equiv.conjRingEquiv (exteriorRepresentation generatorA)) =
    exteriorMatrix false
  second : LinearMap.toMatrix' (equiv.conjRingEquiv (exteriorRepresentation generatorB)) =
    exteriorMatrix true

/-- Seven concrete identities, all in the literal published matrix conventions. -/
structure MatrixCertificates : Prop where
  projection_section : projection * sectionMatrix = 1
  projection_A : projection * exteriorMatrix false = matrixA false * projection
  projection_B : projection * exteriorMatrix true = matrixB false * projection
  dual_left : dualChange * dualChangeInverse = 1
  dual_right : dualChangeInverse * dualChange = 1
  dual_A : dualChange * (matrixA false).transpose = matrixA true * dualChange
  dual_B : dualChange * (matrixB false ^ 2).transpose = matrixB true * dualChange

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.NativeActions
