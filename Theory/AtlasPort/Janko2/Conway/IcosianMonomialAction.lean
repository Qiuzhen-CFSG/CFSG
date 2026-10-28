/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianMonomialAction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianMonomialReduction
public import Theory.AtlasPort.Janko2.Lattices.IcosianGlueFreeCoordinates
public import Theory.AtlasPort.Janko2.Lattices.IcosianHermitianIdentities

/-!
# IcosianMonomialAction

Integral norm-one monomial maps act as rational-linear Hermitian isometries.
Reduction to the finite glue stabilizer proves preservation of the icosian lattice.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianMonomialAction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes Atlas.Lattices
open scoped BigOperators

def icosianMonomialUnits (u : icosianNormOneGroup) : IcosianQuaternionˣ := Unitary.toUnits u.val

def icosianMonomialLinear (g : IcosianUnitMonomial) :
    IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates where
  toFun x i := (icosianMonomialUnits (g.left i) : IcosianQuaternion)*x (g.right.symm i)
  invFun x i := (↑((icosianMonomialUnits (g.left (g.right i)))⁻¹) : IcosianQuaternion)*x (g.right i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' a x := by
    funext i
    exact Algebra.mul_smul_comm (R := ℚ) (A := IcosianQuaternion) a _ _

def icosianMonomialRepresentation : IcosianUnitMonomial →*
    (IcosianRationalCoordinates ≃ₗ[ℚ] IcosianRationalCoordinates) where
  toFun := icosianMonomialLinear
  map_one' := by
    apply LinearEquiv.ext
    intro x
    funext i
    simp [icosianMonomialLinear,icosianMonomialUnits]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    funext i
    change (icosianMonomialUnits (g.left i*h.left (g.right.symm i)) : IcosianQuaternion)*
      x (h.right.symm (g.right.symm i))=_
    simp [icosianMonomialUnits,icosianMonomialLinear,mul_assoc]

theorem icosianMonomialRepresentation_right_linear (g : IcosianUnitMonomial)
    (a : IcosianQuaternion) (x : IcosianRationalCoordinates) :
    icosianMonomialRepresentation g (icosianRightMul x a)=
      icosianRightMul (icosianMonomialRepresentation g x) a := by
  funext i
  exact (mul_assoc _ _ _).symm

theorem icosianMonomialRepresentation_hermitian (g : IcosianUnitMonomial)
    (x y : IcosianRationalCoordinates) :
    icosianHermitian (icosianMonomialRepresentation g x) (icosianMonomialRepresentation g y)=
      icosianHermitian x y := by
  have hu (u : icosianNormOneGroup) (a b : IcosianQuaternion) :
      star ((icosianMonomialUnits u : IcosianQuaternion)*a)*
        ((icosianMonomialUnits u : IcosianQuaternion)*b)=star a*b := by
    calc
      _ = star a*(star (icosianMonomialUnits u : IcosianQuaternion)*
        (icosianMonomialUnits u : IcosianQuaternion))*b := by simp [star_mul,mul_assoc]
      _ = _ := by rw [show star (icosianMonomialUnits u : IcosianQuaternion)*
        (icosianMonomialUnits u : IcosianQuaternion)=1 from Unitary.coe_star_mul_self u.val]; simp
  change (1/2 : ℚ) • (∑ i,star ((icosianMonomialUnits (g.left i) : IcosianQuaternion)*x (g.right.symm i))*
      ((icosianMonomialUnits (g.left i) : IcosianQuaternion)*y (g.right.symm i)))=_
  simp only [hu]
  rw [Equiv.sum_comp g.right.symm (fun i => star (x i)*y i)]
  rfl

def icosianMonomialIntegral (g : IcosianUnitMonomial) (x : IcosianCoordinates) :
    IcosianCoordinates := fun i => icosianNormOneToOrder (g.left i)*x (g.right.symm i)

theorem icosianMonomialIntegral_reduction (g : IcosianUnitMonomial) (x : IcosianCoordinates) :
    (fun i => icosianModuloTwo (icosianMonomialIntegral g x i))=
      icosianMonomialReduction g • (fun i => icosianModuloTwo (x i)) := by
  funext i
  exact map_mul icosianModuloTwo _ _

theorem icosianLiftedMonomial_integral (g : icosianLiftedMonomial)
    (x : IcosianCoordinates) (hx : x ∈ icosianLeechModule) :
    icosianMonomialIntegral g.val x ∈ icosianLeechModule := by
  rw [icosianLeechModule_matrix_glue,icosianMonomialIntegral_reduction]
  exact ((icosianMatrixGlue_stabilizes_iff _).mpr g.property _).mpr
    ((icosianLeechModule_matrix_glue x).mp hx)

theorem icosianLiftedMonomial_lattice (g : icosianLiftedMonomial)
    (x : IcosianRationalCoordinates) (hx : x ∈ rationalIcosianLattice) :
    icosianMonomialRepresentation g.val x ∈ rationalIcosianLattice := by
  obtain ⟨y,hy,rfl⟩ := hx
  exact ⟨icosianMonomialIntegral g.val y,icosianLiftedMonomial_integral g y hy,rfl⟩

end Atlas.Conway
