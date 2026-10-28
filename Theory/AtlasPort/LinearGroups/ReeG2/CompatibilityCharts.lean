module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/CompatibilityCharts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.PointCompatibility
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- A compatible vector outside the affine chart lies on the distinguished line. -/
theorem compatible_zero_first (m : ℕ) {v w : Vector F}
    (h : pointCompatibility m v w) (h0 : v 0 = 0) :
    v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 ∧ v 4 = 0 ∧ v 5 = 0 := by
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  simp only [wedgeCoordinate] at *
  have h1 : v 1 = 0 := by
    by_contra hn
    have hw : w 0 = 0 := by simpa [h0, hn] using s0
    have hs : sigma F m (v 1) = 0 := by simpa [h0, hw] using s1.symm
    exact hn ((map_eq_zero (sigma F m)).mp hs)
  have h2 : v 2 = 0 := by
    by_contra hn
    have hw0 : w 0 = 0 := by simpa [h0, h1, hn] using s1
    have hw1 : w 1 = 0 := by simpa [h0, h1, hw0, hn] using k0
    have hs : sigma F m (v 2) = 0 := by simpa [h1, hw1] using s2.symm
    exact hn ((map_eq_zero (sigma F m)).mp hs)
  have h3 : v 3 = 0 := by
    by_contra hn
    have hw0 : w 0 = 0 := by simpa [h0, h1, h2, hn] using k0
    have hw1 : w 1 = 0 := by simpa [h0, h1, hw0, hn] using k1
    have hw2 : w 2 = 0 := by simpa [h0, h2, hw0, hn] using k2
    have hs : sigma F m (v 3) = 0 := by simpa [h1, h2, hw1, hw2] using s3.symm
    exact hn ((map_eq_zero (sigma F m)).mp hs)
  have h4 : v 4 = 0 := by
    by_contra hn
    have hw0 : w 0 = 0 := by simpa [h0, h1, h3, hn] using k1
    have hw1 : w 1 = 0 := by simpa [h1, h2, hn] using s2
    have hw2 : w 2 = 0 := by simpa [h0, h1, h2, hw0, hw1, hn] using k3
    have hs : sigma F m (v 4) = 0 := by simpa [h2, hw2] using s4.symm
    exact hn ((map_eq_zero (sigma F m)).mp hs)
  have h5 : v 5 = 0 := by
    by_contra hn
    have hw0 : w 0 = 0 := by simpa [h0, h2, h3, hn] using k2
    have hw2 : w 2 = 0 := by simpa [h2, h4, hn] using s4
    have hw1 : w 1 = 0 := by simpa [h0, h1, h2, h4, hw0, hw2, hn] using k3
    have hw3 : w 3 = 0 := by simpa [h2, h3, h4, hw2, hn] using k5
    have hw4 : w 4 = 0 := by simpa [h3, h4, hw3, hn] using k6
    have hs : sigma F m (v 5) = 0 := by simpa [h4, hw4] using s5.symm
    exact hn ((map_eq_zero (sigma F m)).mp hs)
  exact ⟨h1,h2,h3,h4,h5⟩

end Atlas.ReeG2
