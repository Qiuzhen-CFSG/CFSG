module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/PointCompatibility.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.ProjectiveAction
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Coordinates of the exterior product of two row vectors. -/
def wedgeCoordinate (v w : Vector F) (i j : Fin 7) : F := v i * w j - v j * w i

/-- The seven linear relations defining the relevant exterior-square kernel. -/
def exteriorKernel (v w : Vector F) : Prop :=
  wedgeCoordinate v w 0 3 = wedgeCoordinate v w 1 2 ∧
  wedgeCoordinate v w 0 4 = -wedgeCoordinate v w 1 3 ∧
  wedgeCoordinate v w 0 5 = wedgeCoordinate v w 2 3 ∧
  wedgeCoordinate v w 0 6 = wedgeCoordinate v w 1 5 + wedgeCoordinate v w 2 4 ∧
  wedgeCoordinate v w 1 6 = wedgeCoordinate v w 3 4 ∧
  wedgeCoordinate v w 2 6 = -wedgeCoordinate v w 3 5 ∧
  wedgeCoordinate v w 3 6 = wedgeCoordinate v w 4 5

/-- The twisted exterior-square equations in the actual seven-coordinate model. -/
def pointCompatibility (m : ℕ) (v w : Vector F) : Prop :=
  exteriorKernel v w ∧
  wedgeCoordinate v w 0 1 = sigma F m (v 0) ∧
  wedgeCoordinate v w 0 2 = sigma F m (v 1) ∧
  -wedgeCoordinate v w 1 4 = sigma F m (v 2) ∧
  -wedgeCoordinate v w 1 5 + wedgeCoordinate v w 2 4 = sigma F m (v 3) ∧
  -wedgeCoordinate v w 2 5 = sigma F m (v 4) ∧
  wedgeCoordinate v w 4 6 = sigma F m (v 5) ∧
  wedgeCoordinate v w 5 6 = sigma F m (v 6)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem affine_pointCompatibility (m : ℕ) (hcard : Nat.card F = 3 ^ (2 * m + 1))
    (a b c : F) :
    pointCompatibility m (affineVector m a b c) (rootMatrix m a b c 1) := by
  have ha := sigma_eq_theta_cube (F := F) (m := m) a
  have hb := sigma_eq_theta_cube (F := F) (m := m) b
  have hc := sigma_eq_theta_cube (F := F) (m := m) c
  unfold pointCompatibility exteriorKernel
  simp only [affineVector, rootMatrix_expanded, rootExpanded, wedgeCoordinate,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_mul, map_neg, map_pow, map_one, sigma_theta hcard, ha, hb, hc]
  repeat' apply And.intro
  all_goals apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!

end Atlas.ReeG2
