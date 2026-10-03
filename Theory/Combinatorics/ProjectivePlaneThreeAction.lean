module

public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Theory.SpecificGroups.PSL3Three.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The canonical PSL₃(3) collineations and projective frame

The canonical quotient identifies SL₃(3) with PSL₃(3). Transporting the paired
matrix action through this equivalence gives an injective homomorphism into the
full incidence collineation group of PG(2,3). Its point component is Mathlib's
canonical projective action, and its line component is inverse transpose.

The coordinate frame consists of the three coordinate points and `[1,1,1]`.
It is the frame used to recognize all collineations by elementary joins and
intersections, toward Wong, Theorem 6(b), printed p. 111.
-/

namespace Configuration.PlaneThree

open Matrix.PSL3Three
open scoped Matrix

/-- Points of PG(2,3), also used for line covectors under orthogonality incidence. -/
public abbrev PG := Projectivization (ZMod 3) (Fin 3 → ZMod 3)

/-- The full incidence collineation group of the canonical plane. -/
public abbrev FullCollineation := Configuration.Collineation PG PG

/-- The actual canonical PSL matrix action on points and covectors. -/
@[expose] public noncomputable def pslCollineation : PSL →* FullCollineation :=
  specialLinearCollineation.comp equiv.symm.toMonoidHom

@[simp] public theorem pslCollineation_project (A : SL) :
    pslCollineation (project A) = specialLinearCollineation A := by
  change specialLinearCollineation (equiv.symm (project A)) = _
  rw [← equiv_apply, equiv.symm_apply_apply]

/-- The point component agrees with the canonical projective quotient action. -/
@[simp] public theorem pslCollineation_point (g : PSL) (p : PG) :
    Collineation.pointHom PG PG (pslCollineation g) p = g • p := by
  obtain ⟨A, rfl⟩ := project_surjective g
  rw [pslCollineation_project, specialLinearCollineation_point]
  rfl

/-- On line covectors, a determinant-one representative acts by inverse transpose. -/
@[simp] public theorem pslCollineation_line (A : SL) (l : PG) :
    Collineation.lineHom PG PG (pslCollineation (project A)) l =
      Matrix.SpecialLinearGroup.inverseTranspose A • l := by
  rw [pslCollineation_project, specialLinearCollineation_line]

/-- In coordinates, the point action is multiplication of a column vector by the matrix. -/
public theorem pslCollineation_point_mk (A : SL) (v : Fin 3 → ZMod 3) (hv : v ≠ 0) :
    Collineation.pointHom PG PG (pslCollineation (project A))
      (Projectivization.mk (ZMod 3) v hv) =
      Projectivization.mk (ZMod 3) (A.val *ᵥ v) ((smul_ne_zero_iff_ne A).mpr hv) := by
  rw [pslCollineation_project, specialLinearCollineation_point]
  rfl

/-- In coordinates, the line action is multiplication by the inverse transpose. -/
public theorem pslCollineation_line_mk (A : SL) (w : Fin 3 → ZMod 3) (hw : w ≠ 0) :
    Collineation.lineHom PG PG (pslCollineation (project A))
      (Projectivization.mk (ZMod 3) w hw) =
      Projectivization.mk (ZMod 3) ((A⁻¹).val.transpose *ᵥ w)
        ((smul_ne_zero_iff_ne (Matrix.SpecialLinearGroup.inverseTranspose A)).mpr hw) := by
  rw [pslCollineation_line]
  rfl

public theorem pslCollineation_injective : Function.Injective pslCollineation := by
  intro g h heq
  apply eq_of_smul_eq_smul (α := PG)
  intro p
  have hp := congrArg (fun c => Collineation.pointHom PG PG c p) heq
  simpa only [pslCollineation_point] using hp

/-- Nonzero coordinate representatives of the standard ordered frame. -/
@[expose] public def frameVector : Fin 4 → Fin 3 → ZMod 3 :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 1]]

public theorem frameVector_ne_zero (i : Fin 4) : frameVector i ≠ 0 := by
  fin_cases i <;> decide

/-- The three coordinate points followed by the all-ones point. -/
@[expose] public def frame (i : Fin 4) : PG :=
  Projectivization.mk (ZMod 3) (frameVector i) (frameVector_ne_zero i)

end Configuration.PlaneThree
