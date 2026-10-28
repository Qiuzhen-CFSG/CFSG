module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/CrossProduct.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.PointCompatibility
public import Theory.AtlasPort.LinearGroups.ReeG2.InvariantForm
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- The alternating cross product in the fixed seven-coordinate basis. -/
def crossProduct (v w : Vector F) : Vector F :=
  ![wedgeCoordinate v w 0 3 - wedgeCoordinate v w 1 2,
    -wedgeCoordinate v w 0 4 - wedgeCoordinate v w 1 3,
    wedgeCoordinate v w 0 5 - wedgeCoordinate v w 2 3,
    wedgeCoordinate v w 0 6 - wedgeCoordinate v w 1 5 - wedgeCoordinate v w 2 4,
    wedgeCoordinate v w 1 6 - wedgeCoordinate v w 3 4,
    -wedgeCoordinate v w 2 6 - wedgeCoordinate v w 3 5,
    wedgeCoordinate v w 3 6 - wedgeCoordinate v w 4 5]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Coordinate expansion of the seven bilinear identities.
theorem alpha_preserves_crossProduct (m : ℕ) (x : F) (v w : Vector F) :
    crossProduct (rowEquiv (alpha m x) v) (rowEquiv (alpha m x) w) =
      rowEquiv (alpha m x) (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, -theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Coordinate expansion of the seven bilinear identities.
theorem beta_preserves_crossProduct (m : ℕ) (x : F) (v w : Vector F) :
    crossProduct (rowEquiv (beta m x) v) (rowEquiv (beta m x) w) =
      rowEquiv (beta m x) (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, -theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Coordinate expansion of the seven bilinear identities.
theorem gamma_preserves_crossProduct (m : ℕ) (x : F) (v w : Vector F) :
    crossProduct (rowEquiv (gamma m x) v) (rowEquiv (gamma m x) w) =
      rowEquiv (gamma m x) (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ, -theta_apply] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Seven diagonal-weight identities, with nonzero unit denominators.
theorem torus_preserves_crossProduct (m : ℕ) (l : Fˣ) (v w : Vector F) :
    crossProduct (rowEquiv (torus m l) v) (rowEquiv (torus m l) w) =
      rowEquiv (torus m l) (crossProduct v w) := by
  have hl := Units.ne_zero l
  have ht : theta F m (l : F) ≠ 0 := (map_ne_zero (theta F m)).mpr hl
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit,
      torusDiagonal, Matrix.vecMul_diagonal, -theta_apply] <;>
    field_simp <;> ring

theorem upsilon_preserves_crossProduct (v w : Vector F) :
    crossProduct (rowEquiv (upsilon : Ambient F) v) (rowEquiv upsilon w) =
      rowEquiv upsilon (crossProduct v w) := by
  ext i
  fin_cases i <;>
    simp [crossProduct, wedgeCoordinate, rowEquiv_apply, upsilon, upsilonMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;> ring

end Atlas.ReeG2

