module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootMultiplication.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootMatrices
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The root multiplication law in the inverse-Tits convention. -/
theorem rootMatrix_mul (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1))
    (a b c d e f : F) :
    rootMatrix m a b c * rootMatrix m d e f =
      rootMatrix m (a+d) (b+e-a*(theta F m d)^3)
        (c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3) := by
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have ht := theta_square_cube hcard d
  simp only [rootMatrix_expanded]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootExpanded, Matrix.mul_apply,
      Fin.sum_univ_succ, -theta_apply, theta_square_cube hcard] <;>
    apply sub_eq_zero.mp <;> ring_nf <;> reduce_mod_char!
end Atlas.ReeG2
