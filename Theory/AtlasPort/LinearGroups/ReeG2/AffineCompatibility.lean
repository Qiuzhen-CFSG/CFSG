module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/AffineCompatibility.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.PointCompatibility
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Subtracting a multiple of the first vector leaves its exterior product unchanged. -/
theorem pointCompatibility_adjust (m : ℕ) {v w : Vector F}
    (h : pointCompatibility m v w) (t : F) :
    pointCompatibility m v (fun i => w i - t * v i) := by
  have he (i j : Fin 7) : wedgeCoordinate v (fun i => w i - t * v i) i j =
      wedgeCoordinate v w i j := by unfold wedgeCoordinate; ring
  simpa only [pointCompatibility, exteriorKernel, he] using h

set_option maxHeartbeats 800000 in
/-- In the affine chart the first four coordinates determine a compatible vector. -/
theorem pointCompatibility_affine_unique (m : ℕ) {v w v' w' : Vector F}
    (h : pointCompatibility m v w) (h' : pointCompatibility m v' w')
    (hv : v 0 = 1) (hv' : v' 0 = 1) (hw : w 0 = 0) (hw' : w' 0 = 0)
    (h1 : v 1 = v' 1) (h2 : v 2 = v' 2) (h3 : v 3 = v' 3) : v = v' := by
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  rcases h' with ⟨⟨l0,l1,l2,l3,l4,l5,l6⟩,t0,t1,t2,t3,t4,t5,t6⟩
  simp only [wedgeCoordinate, hv, hv', hw, hw', mul_zero, sub_zero, one_mul,
    map_one] at k0 k1 k2 k3 k4 k5 k6 l0 l1 l2 l3 l4 l5 l6 s0 s1 s2 s3 s4 s5 s6 t0 t1 t2 t3 t4 t5 t6
  have w1 : w 1 = w' 1 := s0.trans t0.symm
  have w2 : w 2 = w' 2 := s1.trans ((congrArg (sigma F m) h1).trans t1.symm)
  have w3 : w 3 = w' 3 := by rw [k0,l0,h1,h2,w1,w2]
  have w4 : w 4 = w' 4 := by rw [k1,l1,h1,h3,w1,w3]
  have w5 : w 5 = w' 5 := by rw [k2,l2,h2,h3,w2,w3]
  have v4 : v 4 = v' 4 := by
    rw [h1,w4,s0] at s2
    rw [t0] at t2
    rw [h2] at s2
    linear_combination s2-t2
  have v5 : v 5 = v' 5 := by
    rw [h1,h2,w5,w4,w2,v4,s0,h3] at s3
    rw [t0] at t3
    linear_combination s3-t3
  have w6 : w 6 = w' 6 := by rw [k3,l3,h1,h2,w5,w1,v5,w4,v4,w2]
  have v6 : v 6 = v' 6 := by
    rw [h1,w6,s0,h3,w4,v4,w3] at k4
    rw [t0] at l4
    linear_combination -k4+l4
  ext i
  fin_cases i
  · exact hv.trans hv'.symm
  · exact h1
  · exact h2
  · exact h3
  · exact v4
  · exact v5
  · exact v6


/-- Recovery of the actual root parameters from a normalized compatible vector. -/
theorem compatible_affine_reconstruction (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) {v w : Vector F}
    (h : pointCompatibility m v w) (hv : v 0 = 1) :
    v = affineVector m (sigma F m (v 1)) (-sigma F m (v 2))
      (sigma F m (-(v 1 * v 2) - v 3)) := by
  let a := sigma F m (v 1)
  let b := -sigma F m (v 2)
  let c := sigma F m (-(v 1 * v 2) - v 3)
  apply pointCompatibility_affine_unique m
    (pointCompatibility_adjust m h (w 0)) (affine_pointCompatibility m hcard a b c)
    hv (affineVector_zero m a b c)
  · simp [hv]
  · simp [rootMatrix_expanded, rootExpanded]
  · simp [affineVector, rootMatrix_01, a, theta_sigma hcard, -theta_apply, -sigma_apply]
  · simp [affineVector, rootMatrix_02, b, theta_sigma hcard, -theta_apply, -sigma_apply]
  · simp [affineVector, rootMatrix_03, a, b, c, theta_sigma hcard, -theta_apply, -sigma_apply]

end Atlas.ReeG2

