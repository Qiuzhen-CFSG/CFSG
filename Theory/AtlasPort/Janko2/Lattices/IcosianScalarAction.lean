/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/IcosianScalarAction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Lattices.IcosianScalarStructure
public import Theory.AtlasPort.Janko2.Lattices.IcosianCongruence
public import Theory.AtlasPort.Janko2.Algebra.IcosianNormOneReduction

/-!
# Icosian Scalar Action

Inverse right multiplication defines a representation of the integral
norm-one group. Conjugation invariance preserves the weighted rational
form, and the right-module structure preserves the lattice.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/IcosianScalarAction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0: module/public imports and exposed public
coordinate definitions; concrete carriers and theorem statements are retained.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Lattices
open Atlas.Algebra
open scoped Quaternion

/-- Inverse right multiplication gives the genuine homomorphism convention. -/
def icosianRightUnitEquiv (u : IcosianQuaternionˣ) :
    IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates where
  toFun x := icosianRightMul x (↑(u⁻¹) : IcosianQuaternion)
  invFun x := icosianRightMul x (↑u : IcosianQuaternion)
  left_inv x := by funext i; simp [icosianRightMul,mul_assoc]
  right_inv x := by funext i; simp [icosianRightMul,mul_assoc]
  map_add' x y := by funext i; exact add_mul _ _ _
  map_smul' r x := by funext i; exact Algebra.smul_mul_assoc r (x i) _

def icosianScalarRepresentation : icosianNormOneGroup →*
    (IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates) where
  toFun u := icosianRightUnitEquiv (Unitary.toUnits u.val)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    funext i
    simp [icosianRightUnitEquiv,icosianRightMul]
  map_mul' u v := by
    apply LinearEquiv.ext
    intro x
    funext i
    simp [icosianRightUnitEquiv,icosianRightMul,mul_assoc]

/-- Right norm-one scalars preserve the weighted rational form, although they
conjugate the quaternionic Hermitian form rather than fixing it. -/
theorem icosianScalarRepresentation_bilinear (u : icosianNormOneGroup)
    (x y : IcosianRationalCoordinates) :
    icosianBilinear (icosianScalarRepresentation u x) (icosianScalarRepresentation u y)=
      icosianBilinear x y := by
  change 2*icosianFunctional (icosianHermitian
    (icosianRightMul x (↑(Unitary.toUnits u.val)⁻¹))
    (icosianRightMul y (↑(Unitary.toUnits u.val)⁻¹)))=_
  rw [icosianHermitian_rightMul_left,icosianHermitian_rightMul_right]
  congr 1
  rw [icosianFunctional_mul_comm]
  have hu : (↑((Unitary.toUnits u.val)⁻¹) : IcosianQuaternion) *
      star (↑((Unitary.toUnits u.val)⁻¹) : IcosianQuaternion)=1 := by
    exact Unitary.coe_mul_star_self (u.val⁻¹)
  rw [mul_assoc,hu,mul_one]

/-- The inverse right scalar acts inside the actual integral right module. -/
def icosianCoordinateRightUnit (u : icosianNormOneGroup) (x : IcosianCoordinates) :
    IcosianCoordinates := fun i => x i*icosianNormOneToOrder (u⁻¹)

theorem icosianCoordinateRightUnit_mem (u : icosianNormOneGroup) (x : IcosianCoordinates)
    (hx : x ∈ icosianLeechModule) : icosianCoordinateRightUnit u x ∈ icosianLeechModule :=
  icosianLeechModule.smul_mem (MulOpposite.op (icosianNormOneToOrder (u⁻¹))) hx

theorem icosianScalarRepresentation_lattice (u : icosianNormOneGroup)
    (x : IcosianRationalCoordinates) (hx : x ∈ rationalIcosianLattice) :
    icosianScalarRepresentation u x ∈ rationalIcosianLattice := by
  obtain ⟨y,hy,rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_map.mpr ⟨icosianCoordinateRightUnit u y,
    icosianCoordinateRightUnit_mem u y hy,rfl⟩

theorem icosianScalarRepresentation_lattice_iff (u : icosianNormOneGroup)
    (x : IcosianRationalCoordinates) :
    x ∈ rationalIcosianLattice ↔ icosianScalarRepresentation u x ∈ rationalIcosianLattice := by
  constructor
  · exact icosianScalarRepresentation_lattice u x
  · intro hx
    have h := icosianScalarRepresentation_lattice (u⁻¹) _ hx
    simpa only [map_inv,LinearEquiv.coe_inv,LinearEquiv.symm_apply_apply] using h

end Atlas.Lattices
