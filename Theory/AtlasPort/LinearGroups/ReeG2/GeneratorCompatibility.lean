module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/GeneratorCompatibility.lean, revision
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
-- Seven bilinear transformation identities, reduced in characteristic three.
theorem alpha_preserves_pointCompatibility (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) {v w : Vector F}
    (h : pointCompatibility m v w) :
    pointCompatibility m (rowEquiv (alpha m x) v) (rowEquiv (alpha m x) w) := by
  have hk : exteriorKernel (rowEquiv (alpha m x) v) (rowEquiv (alpha m x) w) := by
    apply (exteriorKernel_iff_crossProduct_zero _ _).mpr
    rw [alpha_preserves_crossProduct, (exteriorKernel_iff_crossProduct_zero _ _).mp h.1]
    exact (rowEquiv (alpha m x)).map_zero
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [wedgeCoordinate] at k0 k1 k2 k3 k4 k5 k6 s0 s1 s2 s3 s4 s5 s6
  have hsx := sigma_eq_theta_cube (F := F) (m := m) x
  refine ⟨hk,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (1) * s0
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (x) * s0 + (1) * s1
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-((theta F m x)^2)) * k0 + (-((theta F m x))) * k1 + ((theta F m x)^3) * s1 + (1) * s2
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (x*(theta F m x)) * k1 + (-((theta F m x))) * k2 + (x*(theta F m x)^3) * s1 + (x) * s2 + (1) * s3
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x^3*(theta F m x)^3)) * s0 + (-(x^2*(theta F m x)^3)) * s1 + (-(x^2)) * s2 + (x) * s3 + (1) * s4
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x^2*(theta F m x)^5)) * k0 + (x^2*(theta F m x)^4) * k1 + (x*(theta F m x)^4) * k2 + (-(x*(theta F m x)^3)) * k3 + (-(x*(theta F m x)^2)) * k4 + (-((theta F m x)^2)) * k5 + ((theta F m x)) * k6 + (-(x^3*(theta F m x)^6)) * s0 + (-((theta F m x)^3)) * s4 + (1) * s5
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, alpha, alphaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x^2*(theta F m x)^3)) * k3 + (x^4*(theta F m x)^6) * s0 + (-(x^3*(theta F m x)^6)) * s1 + (x^3*(theta F m x)^3) * s2 + (x*(theta F m x)^3) * s4 + (-(x)) * s5 + (1) * s6
    all_goals reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Seven bilinear transformation identities, reduced in characteristic three.
theorem beta_preserves_pointCompatibility (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) {v w : Vector F}
    (h : pointCompatibility m v w) :
    pointCompatibility m (rowEquiv (beta m x) v) (rowEquiv (beta m x) w) := by
  have hk : exteriorKernel (rowEquiv (beta m x) v) (rowEquiv (beta m x) w) := by
    apply (exteriorKernel_iff_crossProduct_zero _ _).mpr
    rw [beta_preserves_crossProduct, (exteriorKernel_iff_crossProduct_zero _ _).mp h.1]
    exact (rowEquiv (beta m x)).map_zero
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [wedgeCoordinate] at k0 k1 k2 k3 k4 k5 k6 s0 s1 s2 s3 s4 s5 s6
  have hsx := sigma_eq_theta_cube (F := F) (m := m) x
  refine ⟨hk,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (1) * s0
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (1) * s1
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x)) * s0 + (1) * s2
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-((theta F m x))) * k1 + (x) * s1 + (1) * s3
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) ((theta F m x)^2) * k0 + ((theta F m x)) * k2 + (-((theta F m x)^3)) * s0 + (1) * s4
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x)) * k3 + (-(x^2)) * s1 + (x) * s3 + (1) * s5
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, beta, betaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (x*(theta F m x)^2) * k0 + (x*(theta F m x)) * k2 + (-((theta F m x)^2)) * k4 + ((theta F m x)) * k6 + (-(x*(theta F m x)^3)) * s0 + ((theta F m x)^3) * s2 + (x) * s4 + (1) * s6
    all_goals reduce_mod_char!

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
-- Seven bilinear transformation identities, reduced in characteristic three.
theorem gamma_preserves_pointCompatibility (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) {v w : Vector F}
    (h : pointCompatibility m v w) :
    pointCompatibility m (rowEquiv (gamma m x) v) (rowEquiv (gamma m x) w) := by
  have hk : exteriorKernel (rowEquiv (gamma m x) v) (rowEquiv (gamma m x) w) := by
    apply (exteriorKernel_iff_crossProduct_zero _ _).mpr
    rw [gamma_preserves_crossProduct, (exteriorKernel_iff_crossProduct_zero _ _).mp h.1]
    exact (rowEquiv (gamma m x)).map_zero
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [wedgeCoordinate] at k0 k1 k2 k3 k4 k5 k6 s0 s1 s2 s3 s4 s5 s6
  have hsx := sigma_eq_theta_cube (F := F) (m := m) x
  refine ⟨hk,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (1) * s0
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (1) * s1
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (1) * s2
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x)) * s0 + (1) * s3
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (-(x)) * s1 + (1) * s4
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) ((theta F m x)^2) * k1 + (-((theta F m x))) * k4 + (-((theta F m x)^3)) * s0 + (x) * s2 + (1) * s5
    all_goals reduce_mod_char!
  · simp [wedgeCoordinate, rowEquiv_apply, gamma, gammaMatrix,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      -theta_apply, -sigma_apply, sigma_theta hcard, hsx]
    linear_combination (norm := ring_nf) (x*(theta F m x)) * k0 + ((theta F m x)^2) * k2 + (-(x)) * k3 + ((theta F m x)) * k5 + (-(x^2)) * s0 + ((theta F m x)^3) * s1 + (-(x)) * s3 + (1) * s6
    all_goals reduce_mod_char!

end Atlas.ReeG2
