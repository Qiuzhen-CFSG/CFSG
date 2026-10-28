module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Models
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Displacement
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Diagnostic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# The M22 cocode pair stabilizers and their perfect-residual actions

The source family is a 22-vector nonzero orbit. Its native stabilizer is
PSL(3,4), while the full setwise-pair stabilizer is the genuine extension by
field Frobenius. Both generate the whole cocode by displacements. Perfectness
of the identified PSL subgroup discharges every extra premise in the stronger
solvable-residual displacement conclusions needed by 8.1.1.
The outer group's order 40320 also certifies the mismatch in the literal
outer-stabilizer version of H.15.1(1).

Source: Aschbacher--Smith, H.15.1 and 8.1.1, printed pp.398,712.
-/

public section
noncomputable section
open Sporadic.Mathieu
namespace MathieuCode

/-- The native vector stabilizer is the actual determinant-one projective group. -/
def m22WeightTwoVector_stabilizer_equiv (i : Fin 22) :
    m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i) ≃*
      Matrix.PSL3Four.PSL :=
  (MulEquiv.subgroupCongr (m22WeightTwoVector_stabilizer i)).trans (m22PointStabilizerEquiv i)

/-- The full outer vector stabilizer is the actual extension by field Frobenius. -/
def m22WeightTwoVector_outer_stabilizer_equiv (i : Fin 22) :
    m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i) ≃*
      Matrix.PSL3Four.FieldExtension :=
  (MulEquiv.subgroupCongr (m22WeightTwoVector_outer_stabilizer i)).trans
    (m22OuterPointStabilizerEquiv i)

theorem m22PointStabilizer_perfect (i : Fin 22) :
    Group.IsPerfect (MulAction.stabilizer M22 i) := by
  let : Group.IsPerfect Matrix.PSL3Four.PSL :=
    Atlas.psl_perfect (F := Matrix.PSL3Four.F) 3 (by decide)
  exact Group.IsPerfect.ofSurjective (f := (m22PointStabilizerEquiv i).symm.toMonoidHom)
    (m22PointStabilizerEquiv i).symm.surjective

/-- The native perfect residual supplies every displacement required in 8.1.1. -/
theorem m22WeightTwoVector_residual_commutator (i : Fin 22) :
    Representation.BinaryOffender.subspaceCommutator m22CocodeRepresentation ⊤
      ((Subgroup.solvableResidual
        (m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i))).map
        (m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i)).subtype) = ⊤ := by
  let := m22PointStabilizer_perfect i
  exact m22WeightTwoVector_residual_commutator_of_perfect i

/-- The residual is the actual residual of the full outer stabilizer. -/
theorem m22WeightTwoVector_outer_residual_commutator (i : Fin 22) :
    Representation.BinaryOffender.subspaceCommutator m22OuterCocodeRepresentation ⊤
      ((Subgroup.solvableResidual
        (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i))).map
        (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i)).subtype) = ⊤ := by
  let := m22PointStabilizer_perfect i
  exact m22WeightTwoVector_outer_residual_commutator_of_perfect i

end MathieuCode
