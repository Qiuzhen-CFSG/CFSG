module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/Torus.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Generators
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def torusHom (m : ℕ) : Fˣ →* Ambient F where
  toFun := torus m
  map_one' := by
    apply Units.ext
    change Matrix.diagonal _ = 1
    rw [Matrix.diagonal_eq_one]
    funext i
    fin_cases i <;> simp [torusDiagonal]
  map_mul' := torus_mul m

def splitTorus (m : ℕ) : Subgroup (Ambient F) := (torusHom (F := F) m).range

def torusParameterEquiv (m : ℕ) : Fˣ ≃* splitTorus (F := F) m :=
  MulEquiv.ofBijective (torusHom m).rangeRestrict
    ⟨fun _ _ h => torus_injective m (congrArg Subtype.val h),
      (torusHom m).rangeRestrict_surjective⟩

theorem card_splitTorus (m : ℕ) : Nat.card (splitTorus (F := F) m) = Nat.card F - 1 := by
  rw [← Nat.card_congr (torusParameterEquiv (F := F) m).toEquiv, Nat.card_units]

theorem upsilon_inv : (upsilon : Ambient F)⁻¹ = upsilon :=
  inv_eq_of_mul_eq_one_right upsilon_square

theorem upsilon_torus (m : ℕ) (l : Fˣ) :
    upsilon * torus m l * upsilon⁻¹ = torus m l⁻¹ := by
  have h : (upsilon : Ambient F) * torus m l = torus m l⁻¹ * upsilon := by
    apply Units.ext
    change upsilonMatrix * Matrix.diagonal (fun i => (torusDiagonal m l i : F)) =
      Matrix.diagonal (fun i => (torusDiagonal m l⁻¹ i : F)) * upsilonMatrix
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;>
      simp [upsilonMatrix, torusDiagonal, -theta_apply, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc]
  rw [h, mul_assoc, mul_inv_cancel, mul_one]
end Atlas.ReeG2
