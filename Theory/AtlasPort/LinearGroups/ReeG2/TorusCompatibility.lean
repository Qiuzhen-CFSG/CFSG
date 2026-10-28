module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/TorusCompatibility.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.CrossProductGroup
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Seven twisted diagonal-weight identities.
theorem torus_preserves_pointCompatibility (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (l : Fˣ) {v w : Vector F}
    (h : pointCompatibility m v w) :
    pointCompatibility m (rowEquiv (torus m l) v) (rowEquiv (torus m l) w) := by
  have hk : exteriorKernel (rowEquiv (torus m l) v) (rowEquiv (torus m l) w) := by
    apply (exteriorKernel_iff_crossProduct_zero _ _).mpr
    rw [torus_preserves_crossProduct, (exteriorKernel_iff_crossProduct_zero _ _).mp h.1]
    exact (rowEquiv (torus m l)).map_zero
  rcases h with ⟨_,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [wedgeCoordinate] at s0 s1 s2 s3 s4 s5 s6
  have hl := Units.ne_zero l
  have ht : theta F m (l : F) ≠ 0 := (map_ne_zero (theta F m)).mpr hl
  have hs := sigma_eq_theta_cube (F := F) (m := m) (l : F)
  refine ⟨hk,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) ((l:F)) * s0
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) ((theta F m (l:F))^3/(l:F)) * s1
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) ((l:F)^2/(theta F m (l:F))^3) * s2
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) (1) * s3
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) ((theta F m (l:F))^3/(l:F)^2) * s4
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) ((l:F)/(theta F m (l:F))^3) * s5
  · simp [wedgeCoordinate, rowEquiv_apply, torus, diagonalUnit, torusDiagonal,
      Matrix.vecMul_diagonal, -theta_apply, -sigma_apply, sigma_theta hcard, hs]
    linear_combination (norm := (field_simp; ring)) ((l:F)⁻¹) * s6

end Atlas.ReeG2
