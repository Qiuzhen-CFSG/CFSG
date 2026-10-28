module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/StabilizerFlag.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.CompatibilityGroup
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

/-- Standard vector of the fixed matrix model. -/
def coordinateVector (i : Fin 7) : Vector F := Pi.single i 1

@[simp] theorem rowEquiv_coordinateVector (g : Ambient F) (i : Fin 7) :
    rowEquiv g (coordinateVector i) = g.val i := by
  simp [rowEquiv_apply, coordinateVector, Matrix.single_vecMul, Matrix.row]

theorem infinityVector_eq_coordinateVector :
    (infinityVector : Vector F) = coordinateVector 6 := by
  ext i
  fin_cases i <;> simp [infinityVector,coordinateVector]

theorem infinity_compatible_coordinateVector (m : ℕ) :
    pointCompatibility (F := F) m (coordinateVector 6) (-coordinateVector 5) := by
  simp [pointCompatibility, exteriorKernel, wedgeCoordinate, coordinateVector,
    -sigma_apply]

/-- The twisted equations distinguish the two-dimensional terminal flag. -/
theorem compatible_infinity_support (m : ℕ) (l : Fˣ) {w : Vector F}
    (h : pointCompatibility m (l • (infinityVector : Vector F)) w) :
    w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0 ∧ w 4 = 0 := by
  rcases h with ⟨⟨k0,k1,k2,k3,k4,k5,k6⟩,s0,s1,s2,s3,s4,s5,s6⟩
  have hl := Units.ne_zero l
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [wedgeCoordinate,infinityVector,Units.smul_def,hl] using k3
  · simpa [wedgeCoordinate,infinityVector,Units.smul_def,hl] using k4
  · simpa [wedgeCoordinate,infinityVector,Units.smul_def,hl] using k5
  · simpa [wedgeCoordinate,infinityVector,Units.smul_def,hl] using k6
  · simpa [wedgeCoordinate,infinityVector,Units.smul_def,hl] using s5

set_option maxHeartbeats 800000 in
-- Seven coordinate rows recover the full flag from the two preserved tensors.
theorem infinity_stabilizer_upper_triangular (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (g : Ambient F)
    (hg : g ∈ generated F m) (hfix : pointRight g infinityPoint = infinityPoint) :
    ∀ i j : Fin 7, j < i → g.val i j = 0 := by
  unfold pointRight infinityPoint at hfix
  rw [Projectivization.map_mk] at hfix
  obtain ⟨l,hl⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hfix
  change l • infinityVector = rowEquiv g infinityVector at hl
  have hr6 : g.val 6 = l • infinityVector := by
    simpa only [infinityVector_eq_coordinateVector,rowEquiv_coordinateVector] using hl.symm
  have hc := generated_preserves_pointCompatibility m hcard hg _ _
    (infinity_compatible_coordinateVector (F := F) m)
  rw [rowEquiv_coordinateVector, map_neg, rowEquiv_coordinateVector, hr6] at hc
  obtain ⟨r50,r51,r52,r53,r54⟩ := compatible_infinity_support m l hc
  simp only [Pi.neg_apply,neg_eq_zero] at r50 r51 r52 r53 r54
  have he (i : Fin 7) := generated_preserves_crossProduct m hg (coordinateVector 6) (coordinateVector i)
  simp only [rowEquiv_coordinateVector,hr6] at he
  have e4 : crossProduct (coordinateVector (F := F) 6) (coordinateVector 4) = 0 := by
    ext i; fin_cases i <;> simp [crossProduct,wedgeCoordinate,coordinateVector]
  have e3 : crossProduct (coordinateVector (F := F) 6) (coordinateVector 3) = -coordinateVector 6 := by
    ext i; fin_cases i <;> simp [crossProduct,wedgeCoordinate,coordinateVector]
  have e2 : crossProduct (coordinateVector (F := F) 6) (coordinateVector 2) = coordinateVector 5 := by
    ext i; fin_cases i <;> simp [crossProduct,wedgeCoordinate,coordinateVector]
  have e1 : crossProduct (coordinateVector (F := F) 6) (coordinateVector 1) = -coordinateVector 4 := by
    ext i; fin_cases i <;> simp [crossProduct,wedgeCoordinate,coordinateVector]
  have h4 := he 4
  have h3 := he 3
  have h2 := he 2
  have h1 := he 1
  rw [e4,map_zero] at h4
  rw [e3,map_neg,rowEquiv_coordinateVector,hr6] at h3
  rw [e2,rowEquiv_coordinateVector] at h2
  rw [e1,map_neg,rowEquiv_coordinateVector] at h1
  have hn := Units.ne_zero l
  have r40 : g.val 4 0 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h4 3
  have r41 : g.val 4 1 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h4 4
  have r42 : g.val 4 2 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h4 5
  have r43 : g.val 4 3 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h4 6
  have r30 : g.val 3 0 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h3 3
  have r31 : g.val 3 1 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h3 4
  have r32 : g.val 3 2 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn] using congrFun h3 5
  have r20 : g.val 2 0 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn,r53] using congrFun h2 3
  have r21 : g.val 2 1 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn,r54] using congrFun h2 4
  have r10 : g.val 1 0 = 0 := by simpa [crossProduct,wedgeCoordinate,infinityVector,Units.smul_def,hn,r43] using congrFun h1 3
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [r10,r20,r21,r30,r31,r32,r40,r41,r42,r43,r50,r51,r52,r53,r54,hr6,infinityVector,Units.smul_def] at hij ⊢

end Atlas.ReeG2
