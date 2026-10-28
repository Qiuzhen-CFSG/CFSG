/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Changes: Lean 4.33 modules, narrow imports, and CFSG quadratic-isometry carriers.
-/
module

public import Theory.SpecificGroups.ClassicalOrthogonal.RankOneComparison.Action
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Mathlib.Tactic.LinearCombination

/-!
# Rank-one Siegel roots from SL₂ transvections

Adapted from ATLAS `LinearGroups/Orthogonal/B1ConjugationRoots.lean`.
Compute the conjugation action of the upper and lower transvections in
CFSG's coordinates. These are precisely the standard Siegel transformations
for the unhalved polar form, in every characteristic. They are the root
calculations in the B₁/A₁ comparison of GLS3 §2.7.
-/
@[expose] public noncomputable section
namespace ClassicalOrthogonal.RankOneComparison
open ClassicalOrthogonal.Quadratic Matrix
variable {F : Type*} [Field F]

theorem standard_siegel_image (v : VectorB 1 F)
    (hv : (formB 1 F).polarBilin (e 0,0) v = 0) :
    siegelElement (formB 1 F) (e 0,0) v (by simp [e]) hv =
      toOrthogonal (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-v.2)) := by
  have hv0 : v.1 (.inr 0) = 0 := by
    have hh := hv
    simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e] at hh
    linear_combination hh
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · ext i
    rcases i with i|i <;> fin_cases i
    all_goals
      change (siegel (formB 1 F) (e 0,0) v x).1 _ = _
      simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e,
        hv0,toOrthogonal,onB,coordinates,kernelAction,kernelMap,
        SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
        Fin.sum_univ_two]
      <;> ring
  · change (siegel (formB 1 F) (e 0,0) v x).2 = _
    simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,e,
      hv0,toOrthogonal,onB,coordinates,kernelAction,kernelMap,
      SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
      Fin.sum_univ_two]
    ring

theorem lower_transvection_root (a : F) :
    toOrthogonal (SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) a) =
      siegelElement (formB 1 F) (f 0,0) (0,a) (by simp [f]) (by
        simp [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,f]) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Prod.ext
  · ext i
    rcases i with i|i <;> fin_cases i
    all_goals
      change _ = (siegel (formB 1 F) (f 0,0) (0,a) x).1 _
      simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,f,
        toOrthogonal,onB,coordinates,kernelAction,kernelMap,
        SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
        Fin.sum_univ_two]
      <;> ring
  · change _ = (siegel (formB 1 F) (f 0,0) (0,a) x).2
    simp [siegel,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,formB_apply,formD_apply,f,
      toOrthogonal,onB,coordinates,kernelAction,kernelMap,
      SpecialLinearGroup.transvection_coe,Matrix.adjugate_fin_two,Matrix.mul_apply,
      Fin.sum_univ_two]
    ring

end ClassicalOrthogonal.RankOneComparison
