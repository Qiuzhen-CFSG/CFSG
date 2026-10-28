module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootMatrices.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Generators
set_option warningAsError false

@[expose] public section

/-! Explicit root normal-form matrices, without any group-order premise. -/
noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def rootMatrix (m : ℕ) (a b c : F) : Mat F :=
  alphaMatrix m a * betaMatrix m b * gammaMatrix m c

def rootElement (m : ℕ) (a b c : F) : Ambient F := alpha m a * beta m b * gamma m c

@[simp] theorem rootElement_val (m : ℕ) (a b c : F) :
    (rootElement m a b c).val = rootMatrix m a b c := rfl

theorem rootMatrix_zero (m : ℕ) : rootMatrix (F := F) m 0 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, alphaMatrix, betaMatrix, gammaMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

theorem rootMatrix_01 (m : ℕ) (a b c : F) : rootMatrix m a b c 0 1 = theta F m a := by
  simp [rootMatrix, alphaMatrix, betaMatrix, gammaMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
theorem rootMatrix_02 (m : ℕ) (a b c : F) : rootMatrix m a b c 0 2 = -theta F m b := by
  simp [rootMatrix, alphaMatrix, betaMatrix, gammaMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
theorem rootMatrix_03 (m : ℕ) (a b c : F) :
    rootMatrix m a b c 0 3 = theta F m a * theta F m b - theta F m c := by
  simp [rootMatrix, alphaMatrix, betaMatrix, gammaMatrix, Matrix.mul_apply, Fin.sum_univ_succ]
  ring

theorem rootMatrix_injective (m : ℕ) : Function.Injective
    (fun p : F × F × F => rootMatrix m p.1 p.2.1 p.2.2) := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
  have ha := congrFun (congrFun h 0) 1
  have hb := congrFun (congrFun h 0) 2
  have hc := congrFun (congrFun h 0) 3
  simp only [rootMatrix_01] at ha
  simp only [rootMatrix_02, neg_inj] at hb
  have had := (theta F m).injective ha
  have hbe := (theta F m).injective hb
  subst d; subst e
  simp only [rootMatrix_03, sub_right_inj] at hc
  have hcf := (theta F m).injective hc
  subst f
  rfl

def rootExpanded (m : ℕ) (a b c : F) : Mat F :=
  let ta := theta F m a
  let tb := theta F m b
  let tc := theta F m c
  !![1, ta, -(tb), -(tc) + ta*tb, -(ta*tc) + -(b) + -(a*ta^3), -(tb*tc) + -(ta*tb^2) + -(c) + -(a^2*ta^3), -(tc^2) + -(ta*tb*tc) + c*ta + -(b*tb) + -(a*ta^3*tb) + a^2*ta^4;
     0, 1, a, tb + a*ta, -(tc) + -(a*ta^2), -(tb^2) + a*tc + a*ta*tb, -(tb*tc) + c + -(a*ta*tc) + -(a*ta^2*tb) + a*b + -(a^2*ta^3);
     0, 0, 1, ta, -(ta^2), tc + ta*tb, -(ta*tc) + -(ta^2*tb) + b + a*ta^3;
     0, 0, 0, 1, ta, tb, -(tc) + ta*tb;
     0, 0, 0, 0, 1, -(a), tb + a*ta;
     0, 0, 0, 0, 0, 1, -(ta);
     0, 0, 0, 0, 0, 0, 1]

theorem rootMatrix_expanded (m : ℕ) (a b c : F) :
    rootMatrix m a b c = rootExpanded m a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, rootExpanded, alphaMatrix, betaMatrix, gammaMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, -theta_apply] <;> ring

end Atlas.ReeG2
