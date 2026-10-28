module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/TwoPointDiagonal.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.StabilizerFlag
public import Theory.AtlasPort.LinearGroups.ReeG2.PointTransitivity
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

set_option maxHeartbeats 1600000 in
-- Expansion of the fixed antidiagonal conjugation in 49 coordinates.
theorem upsilon_conjugate_entry (g : Ambient F) (i j : Fin 7) :
    (upsilon * g * upsilon).val i j = g.val i.rev j.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [upsilon,upsilonMatrix,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

/-- Fixing the two distinguished lines forces a diagonal matrix. -/
theorem two_point_stabilizer_diagonal (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (g : Ambient F)
    (hg : g ∈ generated F m) (hfix : pointRight g infinityPoint = infinityPoint)
    (hzero : pointRight g (affinePoint m 0 0 0) = affinePoint m 0 0 0) :
    ∀ i j : Fin 7, i ≠ j → g.val i j = 0 := by
  have hu := infinity_stabilizer_upper_triangular m hcard g hg hfix
  have hmem : upsilon*g*upsilon ∈ generated F m :=
    (generated F m).mul_mem ((generated F m).mul_mem (upsilon_mem_generated m) hg)
      (upsilon_mem_generated m)
  have hconj : pointRight (upsilon*g*upsilon) infinityPoint = infinityPoint := by
    rw [pointRight_mul,pointRight_mul]
    change pointRight upsilon (pointRight g (pointRight upsilon infinityPoint)) = _
    rw [pointRight_infinity_upsilon m,hzero,pointRight_zero_upsilon]
  have hl := infinity_stabilizer_upper_triangular m hcard _ hmem hconj
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · have hh := hl i.rev j.rev (by simpa using h)
    simpa only [upsilon_conjugate_entry,Fin.rev_rev] using hh
  · exact hu i j h

end Atlas.ReeG2
