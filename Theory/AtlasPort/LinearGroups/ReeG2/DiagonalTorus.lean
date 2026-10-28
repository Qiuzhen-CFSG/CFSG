module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/DiagonalTorus.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.TwoPointDiagonal
public import Theory.AtlasPort.LinearGroups.ReeG2.Torus
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]

set_option maxHeartbeats 1200000 in
-- The seven diagonal entries are recovered from the two invariant tensors.
theorem diagonal_generated_mem_torus (m : ℕ)
    (hcard : Nat.card F = 3 ^ (2 * m + 1)) (g : Ambient F)
    (hg : g ∈ generated F m) (hd : ∀ i j : Fin 7, i ≠ j → g.val i j = 0) :
    g ∈ splitTorus (F := F) m := by
  let d : Fin 7 → F := fun i => g.val i i
  have hr (i : Fin 7) : rowEquiv g (coordinateVector i) = d i • coordinateVector i := by
    rw [rowEquiv_coordinateVector]
    ext j
    by_cases hij : i = j
    · subst j
      simp [coordinateVector,d]
    · simp [coordinateVector,Pi.single_apply,hij,Ne.symm hij,hd i j hij]
  have hn (i : Fin 7) : d i ≠ 0 := by
    intro hi
    have he : rowEquiv g (coordinateVector i) = rowEquiv g 0 := by rw [hr,hi,zero_smul,map_zero]
    have hz := (rowEquiv g).injective he
    have hh := congrFun hz i
    simpa [coordinateVector] using hh
  have hc := generated_preserves_crossProduct m hg
  have e03 := hc (coordinateVector 0) (coordinateVector 3)
  have e06 := hc (coordinateVector 0) (coordinateVector 6)
  have e15 := hc (coordinateVector 1) (coordinateVector 5)
  have e24 := hc (coordinateVector 2) (coordinateVector 4)
  have e12 := hc (coordinateVector 1) (coordinateVector 2)
  rw [hr,hr] at e03 e06 e15 e24 e12
  have h03 : d 0 * d 3 = d 0 := by
    simpa [crossProduct,wedgeCoordinate,coordinateVector,rowEquiv_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_succ,d] using congrFun e03 0
  have h06 : d 0 * d 6 = d 3 := by
    simpa [crossProduct,wedgeCoordinate,coordinateVector,rowEquiv_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_succ,d] using congrFun e06 3
  have h15 : d 1 * d 5 = d 3 := by
    simpa [crossProduct,wedgeCoordinate,coordinateVector,rowEquiv_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_succ,d] using congrFun e15 3
  have h24 : d 2 * d 4 = d 3 := by
    simpa [crossProduct,wedgeCoordinate,coordinateVector,rowEquiv_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_succ,d] using congrFun e24 3
  have h12 : d 1 * d 2 = d 0 := by
    simpa [crossProduct,wedgeCoordinate,coordinateVector,rowEquiv_apply,
      Matrix.vecMul,dotProduct,Fin.sum_univ_succ,d] using congrFun e12 0
  have h3 : d 3 = 1 := (mul_left_cancel₀ (hn 0)) (by simpa using h03)
  rw [h3] at h06 h15 h24
  have hb : pointCompatibility (F := F) m (coordinateVector 0) (coordinateVector 1) := by
    simp [pointCompatibility,exteriorKernel,wedgeCoordinate,coordinateVector,-sigma_apply]
  have hh := generated_preserves_pointCompatibility m hcard hg _ _ hb
  have h01 : d 0 * d 1 = sigma F m (d 0) := by
    simpa [hr,wedgeCoordinate,coordinateVector,hd,d,-sigma_apply] using hh.2.1
  let l : Fˣ := Units.mk0 (sigma F m (d 0)) ((map_ne_zero (sigma F m)).mpr (hn 0))
  have ht : theta F m (l : F) = d 0 := theta_sigma hcard (d 0)
  have hl : (l : F) = d 0 * d 1 := h01.symm
  have h2 : d 2 * (l : F) = d 0 ^ 2 := by rw [hl]; linear_combination (d 0) * h12
  have h4 : d 4 * d 0 ^ 2 = (l : F) := by linear_combination (l : F) * h24 - (d 4) * h2
  have h5 : d 5 * (l : F) = d 0 := by rw [hl]; linear_combination (d 0) * h15
  refine ⟨l,?_⟩
  change torus m l = g
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torus,diagonalUnit,torusDiagonal,ht,hd,-theta_apply]
  all_goals change _ = d _
  all_goals field_simp [hn]
  all_goals first
    | exact h3.symm
    | linear_combination -h2
    | linear_combination -h4
    | linear_combination -h5
    | linear_combination -h06
    | linear_combination hl

end Atlas.ReeG2
