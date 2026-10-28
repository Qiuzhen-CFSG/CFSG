/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionDiagonalImage.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionPermutationImage

/-!
# IcosianReflectionDiagonalImage

Diagonal, unipotent, and permutation images generate the full finite glue stabilizer.
Together with the sign kernel, this puts the full frame stabilizer in the reflection
subgroup.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionDiagonalImage.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

def icosianGlueDiagonal (s : GoldenFourˣ) : IcosianGlueMonomialGroup GoldenFour :=
  SemidirectProduct.inl (icosianGlueBlockParameter s 0 0)

def icosianReflectionDiagonalParameter : GoldenFourˣ :=
  Units.mk0 (goldenFourTau+1) (by decide +kernel)

theorem icosianReflection_unipotent_image (a b : GoldenFour) :
    icosianGlueUnipotent a b∈icosianReflectionGlueImage := by
  simpa only [icosianGlueUnipotent_mul,add_zero,zero_add] using
    icosianReflectionGlueImage.mul_mem
      (icosianReflection_unipotent_first a) (icosianReflection_unipotent_second b)

theorem icosianReflectionDiagonal_reduction_factor :
    icosianMonomialReduction icosianReflectionDiagonalMonomial=
      icosianGlueDiagonal icosianReflectionDiagonalParameter *
        icosianGlueUnipotent goldenFourTau (goldenFourTau+1) *
          SemidirectProduct.inr icosianReflectionDiagonalPermutation := by
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    rw [icosianReflectionDiagonalMonomial_reduction]
    simp only [icosianGlueDiagonal, icosianGlueUnipotent, SemidirectProduct.mul_left,
      SemidirectProduct.mul_right, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      SemidirectProduct.left_inr, map_one, MulAut.one_apply, mul_one]
    change _=(icosianGlueBlockParameter icosianReflectionDiagonalParameter 0 0 i).val *
      (icosianGlueBlockParameter 1 goldenFourTau (goldenFourTau+1) i).val
    ext j k <;>
      fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  · rfl

theorem icosianReflection_diagonal_generator_image :
    icosianGlueDiagonal icosianReflectionDiagonalParameter∈icosianReflectionGlueImage := by
  have hg := icosianReflectionGlueImage_mem_of_actual_word _ _
    icosianReflectionDiagonalWord_mem_reflections icosianReflectionDiagonalWord_linear
  have hp := icosianReflection_permutation_image icosianReflectionDiagonalPermutation
  have hu := icosianReflection_unipotent_image goldenFourTau (goldenFourTau+1)
  have h := icosianReflectionGlueImage.mul_mem
    (icosianReflectionGlueImage.mul_mem hg (icosianReflectionGlueImage.inv_mem hp))
      (icosianReflectionGlueImage.inv_mem hu)
  simpa only [icosianReflectionDiagonal_reduction_factor,mul_inv_cancel_right] using h

theorem icosianGlueDiagonal_mul (s t : GoldenFourˣ) :
    icosianGlueDiagonal s*icosianGlueDiagonal t=icosianGlueDiagonal (s*t) := by
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    change (icosianGlueBlockParameter s 0 0 i).val *
      (icosianGlueBlockParameter t 0 0 i).val=(icosianGlueBlockParameter (s*t) 0 0 i).val
    ext j k <;>
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [icosianGlueBlockParameter,icosianGlueMatrix,Matrix.mul_apply,Fin.sum_univ_succ,
        mul_inv_rev,mul_comm]
  · rfl

theorem icosianGlueDiagonal_one : icosianGlueDiagonal 1=1 := by
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    ext j k <;>
      fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel
  · rfl

/-- Only the three units of F4 occur; the order-three scalar generates them. -/
theorem icosianReflectionDiagonal_unit_cases : ∀ s : GoldenFourˣ,
    s=1 ∨ s=icosianReflectionDiagonalParameter ∨
      s=icosianReflectionDiagonalParameter*icosianReflectionDiagonalParameter := by decide +kernel

theorem icosianReflection_diagonal_image (s : GoldenFourˣ) :
    icosianGlueDiagonal s∈icosianReflectionGlueImage := by
  rcases icosianReflectionDiagonal_unit_cases s with rfl | rfl | rfl
  · rw [icosianGlueDiagonal_one]
    exact icosianReflectionGlueImage.one_mem
  · exact icosianReflection_diagonal_generator_image
  · rw [← icosianGlueDiagonal_mul]
    exact icosianReflectionGlueImage.mul_mem
      icosianReflection_diagonal_generator_image icosianReflection_diagonal_generator_image

theorem icosian_full_glue_generated_by_reflections :
    icosianGlueMonomialStabilizer GoldenFour≤ icosianReflectionGlueImage :=
  icosianGlueMonomialStabilizer_le_of_generators _
    icosianReflection_diagonal_image icosianReflection_unipotent_first
    icosianReflection_unipotent_second icosianReflection_permutation_image

/-- Generation of the entire actual coordinate-frame stabilizer. -/
theorem icosian_full_frame_generated_by_reflections :
    icosianCoordinateFrameStabilizer≤ icosianReflectionGroup :=
  icosianFrame_le_reflections_of_glue icosian_full_glue_generated_by_reflections

end Atlas.Conway
