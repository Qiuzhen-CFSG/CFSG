module

public import Theory.Representation.SL2FourNaturalOrbits.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Checked words for the four-relator matrix marking

Over the computable quadratic field F₄, the matrices `A`, `B` satisfy the
(5,5,3) relations, and the mixed word is the scalar `z I`. Six further words
recover x₀₁(1), x₀₁(z), x₁₂(1), x₁₂(z), x₂₀(1), and x₂₀(z).

Each intermediate product is checked separately by the Lean kernel. The
reproducible witness generator is `source/generate.py`; its Python arithmetic
is only used to propose matrices, never as a proof oracle. The field's actual
isomorphism to `GaloisField 2 2` is supplied by `SL2FourNaturalOrbits.Model`.

The relators are from Campbell–Havas–Ramsay–Robertson (2004), Table 2 and §5.11,
https://staff.itee.uq.edu.au/havas/2004chrr.pdf. Capitals in the printed words
denote inverses. Crucially, the mixed word is central, not the identity in SL.
-/

@[expose] public section

namespace Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.MatrixMarking
open Matrix.SpecialLinearGroup
abbrev F := Representation.SL2FourNatural.F
abbrev SL := SpecialLinearGroup (Fin 3) F
def z : F := ⟨0, 1⟩

def A : SL := ⟨!![1, 1, 1; 0, z, z + 1; 1, 0, 0], by decide +kernel⟩

def B : SL := ⟨!![0, 0, z + 1; z + 1, z + 1, z; z, 1, 0], by decide +kernel⟩

private def inverseA : SL := ⟨!![0, 0, 1; z + 1, 1, z + 1; z, 1, z], by decide +kernel⟩

private def inverseB : SL := ⟨!![z, z + 1, z; z + 1, 1, z; z, 0, 0], by decide +kernel⟩

private theorem inv_A : A⁻¹ = inverseA := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  decide +kernel

private theorem inv_B : B⁻¹ = inverseB := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  decide +kernel

def scalarZ : SL := ⟨!![z, 0, 0; 0, z, 0; 0, 0, z], by decide +kernel⟩

private def step0 : SL := ⟨!![0, z + 1, z; z + 1, z + 1, 1; 1, 1, 1], by decide +kernel⟩

private theorem step0_eq : A * A = step0 := by
  apply Subtype.ext
  decide +kernel

private def step1 : SL := ⟨!![z, 1, z; z, z, 1; 0, z + 1, z], by decide +kernel⟩

private theorem step1_eq : step0 * A = step1 := by
  apply Subtype.ext
  decide +kernel

private def step2 : SL := ⟨!![0, 0, 1; z + 1, 1, z + 1; z, 1, z], by decide +kernel⟩

private theorem step2_eq : step1 * A = step2 := by
  apply Subtype.ext
  decide +kernel

private def step3 : SL := ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

private theorem step3_eq : step2 * A = step3 := by
  apply Subtype.ext
  decide +kernel

private theorem fifthA_word : A * A * A * A * A = 1 := by

  rw [step0_eq, step1_eq, step2_eq, step3_eq]

  apply Subtype.ext
  decide +kernel

private def step4 : SL := ⟨!![1, z + 1, 0; 1, 0, z + 1; z + 1, z + 1, z + 1], by decide +kernel⟩

private theorem step4_eq : B * B = step4 := by
  apply Subtype.ext
  decide +kernel

private def step5 : SL := ⟨!![z, z, z; 1, z + 1, z + 1; z + 1, 1, z + 1], by decide +kernel⟩

private theorem step5_eq : step4 * B = step5 := by
  apply Subtype.ext
  decide +kernel

private def step6 : SL := ⟨!![z, z + 1, z; z + 1, 1, z; z, 0, 0], by decide +kernel⟩

private theorem step6_eq : step5 * B = step6 := by
  apply Subtype.ext
  decide +kernel

private def step7 : SL := ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

private theorem step7_eq : step6 * B = step7 := by
  apply Subtype.ext
  decide +kernel

private theorem fifthB_word : B * B * B * B * B = 1 := by

  rw [step4_eq, step5_eq, step6_eq, step7_eq]

  apply Subtype.ext
  decide +kernel

private def step8 : SL := ⟨!![1, z, 1; 0, z, z + 1; 0, 0, z + 1], by decide +kernel⟩

private theorem step8_eq : A * B = step8 := by
  apply Subtype.ext
  decide +kernel

private def step9 : SL := ⟨!![0, z, 0; z + 1, z + 1, 1; z + 1, 0, 0], by decide +kernel⟩

private theorem step9_eq : step8 * A = step9 := by
  apply Subtype.ext
  decide +kernel

private def step10 : SL := ⟨!![1, 1, z + 1; 0, z + 1, z + 1; 0, 0, z], by decide +kernel⟩

private theorem step10_eq : step9 * B = step10 := by
  apply Subtype.ext
  decide +kernel

private def step11 : SL := ⟨!![z, z + 1, z; z + 1, 1, z; z, 0, 0], by decide +kernel⟩

private theorem step11_eq : step10 * A = step11 := by
  apply Subtype.ext
  decide +kernel

private def step12 : SL := ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

private theorem step12_eq : step11 * B = step12 := by
  apply Subtype.ext
  decide +kernel

private theorem cubeAB_word : A * B * A * B * A * B = 1 := by

  rw [step8_eq, step9_eq, step10_eq, step11_eq, step12_eq]

  apply Subtype.ext
  decide +kernel

private def step13 : SL := ⟨!![1, z + 1, 1; 1, 1, 0; z + 1, z, 0], by decide +kernel⟩

private theorem step13_eq : step0 * inverseB = step13 := by
  apply Subtype.ext
  decide +kernel

private def step14 : SL := ⟨!![z, 0, z + 1; 1, z, 0; 0, 0, z], by decide +kernel⟩

private theorem step14_eq : step13 * inverseB = step14 := by
  apply Subtype.ext
  decide +kernel

private def step15 : SL := ⟨!![1, z + 1, z + 1; 1, z, 0; z + 1, z, z + 1], by decide +kernel⟩

private theorem step15_eq : step14 * inverseA = step15 := by
  apply Subtype.ext
  decide +kernel

private def step16 : SL := ⟨!![1, 0, z + 1; z + 1, 1, 1; 1, 0, z], by decide +kernel⟩

private theorem step16_eq : step15 * inverseB = step16 := by
  apply Subtype.ext
  decide +kernel

private def step17 : SL := ⟨!![z, 1, 1; z, 1, 0; z + 1, 1, 1], by decide +kernel⟩

private theorem step17_eq : step16 * A = step17 := by
  apply Subtype.ext
  decide +kernel

private def step18 : SL := ⟨!![z, 0, 1; 0, 0, 1; 0, z + 1, z + 1], by decide +kernel⟩

private theorem step18_eq : step17 * inverseB = step18 := by
  apply Subtype.ext
  decide +kernel

private def step19 : SL := ⟨!![1, 1, z + 1; z, 0, 0; z + 1, z + 1, 1], by decide +kernel⟩

private theorem step19_eq : step18 * inverseB = step19 := by
  apply Subtype.ext
  decide +kernel

private def step20 : SL := ⟨!![z, z + 1, z; z, z, z; z, z, 1], by decide +kernel⟩

private theorem step20_eq : step19 * A = step20 := by
  apply Subtype.ext
  decide +kernel

private def step21 : SL := ⟨!![1, 0, 0; z, z + 1, z; z + 1, 0, z], by decide +kernel⟩

private theorem step21_eq : step20 * B = step21 := by
  apply Subtype.ext
  decide +kernel

private def step22 : SL := ⟨!![0, 0, 1; 1, 1, z + 1; z + 1, z, 0], by decide +kernel⟩

private theorem step22_eq : step21 * inverseA = step22 := by
  apply Subtype.ext
  decide +kernel

private def step23 : SL := ⟨!![z, 0, 0; 0, z, 0; 0, 0, z], by decide +kernel⟩

private theorem step23_eq : step22 * inverseB = step23 := by
  apply Subtype.ext
  decide +kernel

private theorem mixedAB_word : A * A * B⁻¹ * B⁻¹ * A⁻¹ * B⁻¹ * A * B⁻¹ * B⁻¹ * A * B * A⁻¹ * B⁻¹ = scalarZ := by

  rw [inv_A, inv_B]

  rw [step0_eq, step13_eq, step14_eq, step15_eq, step16_eq, step17_eq, step18_eq, step19_eq, step20_eq, step21_eq, step22_eq, step23_eq]

  apply Subtype.ext
  decide +kernel

private def step24 : SL := ⟨!![z + 1, z, 0; 0, z, z + 1; z, z + 1, z], by decide +kernel⟩

private theorem step24_eq : A * inverseB = step24 := by
  apply Subtype.ext
  decide +kernel

private def step25 : SL := ⟨!![z + 1, 0, z; z + 1, z + 1, 1; 0, z + 1, 0], by decide +kernel⟩

private theorem step25_eq : step24 * A = step25 := by
  apply Subtype.ext
  decide +kernel

private def step26 : SL := ⟨!![z, z, 1; 1, 1, 0; z, z + 1, 1], by decide +kernel⟩

private theorem step26_eq : step25 * inverseB = step26 := by
  apply Subtype.ext
  decide +kernel

private def step27 : SL := ⟨!![z + 1, 1, z + 1; 1, z + 1, z; z + 1, z + 1, 0], by decide +kernel⟩

private theorem step27_eq : step26 * A = step27 := by
  apply Subtype.ext
  decide +kernel

private def step28 : SL := ⟨!![z + 1, z + 1, z + 1; z + 1, 0, z + 1; z + 1, 1, 0], by decide +kernel⟩

private theorem step28_eq : step27 * inverseB = step28 := by
  apply Subtype.ext
  decide +kernel

private def step29 : SL := ⟨!![z, 1, 0; 0, z, 1; z, z + 1, z + 1], by decide +kernel⟩

private theorem step29_eq : step28 * inverseB = step29 := by
  apply Subtype.ext
  decide +kernel

private def step30 : SL := ⟨!![z + 1, 1, 1; z + 1, z + 1, z + 1; z + 1, 0, 1], by decide +kernel⟩

private theorem step30_eq : step29 * inverseA = step30 := by
  apply Subtype.ext
  decide +kernel

private def step31 : SL := ⟨!![1, z, 0; z + 1, 1, z + 1; z, 1, z], by decide +kernel⟩

private theorem step31_eq : step30 * B = step31 := by
  apply Subtype.ext
  decide +kernel

private def step32 : SL := ⟨!![1, z, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

private theorem step32_eq : step31 * A = step32 := by
  apply Subtype.ext
  decide +kernel

theorem root01Z_word : A * B⁻¹ * A * B⁻¹ * A * B⁻¹ * B⁻¹ * A⁻¹ * B * A = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) z := by

  rw [inv_A, inv_B]

  rw [step24_eq, step25_eq, step26_eq, step27_eq, step28_eq, step29_eq, step30_eq, step31_eq, step32_eq]

  apply Subtype.ext
  decide +kernel

private def step33 : SL := ⟨!![z, z + 1, z + 1; 1, z + 1, 0; z + 1, 0, 0], by decide +kernel⟩

private theorem step33_eq : step4 * inverseA = step33 := by
  apply Subtype.ext
  decide +kernel

private def step34 : SL := ⟨!![z + 1, 1, 0; z, z, z; 0, 0, z], by decide +kernel⟩

private theorem step34_eq : step33 * B = step34 := by
  apply Subtype.ext
  decide +kernel

private def step35 : SL := ⟨!![z + 1, 1, 0; 0, 1, z + 1; z, 0, 0], by decide +kernel⟩

private theorem step35_eq : step34 * A = step35 := by
  apply Subtype.ext
  decide +kernel

private def step36 : SL := ⟨!![z + 1, 1, 0; z + 1, z, z + 1; z, z, z], by decide +kernel⟩

private theorem step36_eq : step35 * A = step36 := by
  apply Subtype.ext
  decide +kernel

private def step37 : SL := ⟨!![z + 1, z + 1, 0; 0, z, 1; z, z + 1, z], by decide +kernel⟩

private theorem step37_eq : step36 * B = step37 := by
  apply Subtype.ext
  decide +kernel

private def step38 : SL := ⟨!![z, z, z + 1; z + 1, 0, z + 1; 1, 0, 0], by decide +kernel⟩

private theorem step38_eq : step37 * B = step38 := by
  apply Subtype.ext
  decide +kernel

private def step39 : SL := ⟨!![1, 1, z + 1; 0, z + 1, z + 1; 1, 1, 1], by decide +kernel⟩

private theorem step39_eq : step38 * A = step39 := by
  apply Subtype.ext
  decide +kernel

private def step40 : SL := ⟨!![z, z + 1, z; z + 1, 1, z; 0, z + 1, z], by decide +kernel⟩

private theorem step40_eq : step39 * A = step40 := by
  apply Subtype.ext
  decide +kernel

private def step41 : SL := ⟨!![1, 0, 0; 0, 1, 0; 1, 0, 1], by decide +kernel⟩

private theorem step41_eq : step40 * B = step41 := by
  apply Subtype.ext
  decide +kernel

theorem root20One_word : B * B * A⁻¹ * B * A * A * B * B * A * A * B = Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) 1 := by

  rw [inv_A]

  rw [step4_eq, step33_eq, step34_eq, step35_eq, step36_eq, step37_eq, step38_eq, step39_eq, step40_eq, step41_eq]

  apply Subtype.ext
  decide +kernel

private def step42 : SL := ⟨!![0, z, 1; z + 1, 1, z; 1, z, z], by decide +kernel⟩

private theorem step42_eq : step13 * inverseA = step42 := by
  apply Subtype.ext
  decide +kernel

private def step43 : SL := ⟨!![z + 1, 0, z + 1; 0, 1, 0; z, z + 1, 0], by decide +kernel⟩

private theorem step43_eq : step42 * B = step43 := by
  apply Subtype.ext
  decide +kernel

private def step44 : SL := ⟨!![1, z + 1, z; z + 1, 1, z + 1; z, z + 1, 0], by decide +kernel⟩

private theorem step44_eq : step43 * inverseA = step44 := by
  apply Subtype.ext
  decide +kernel

private def step45 : SL := ⟨!![1, 0, z; z, 0, 0; z, z, 0], by decide +kernel⟩

private theorem step45_eq : step44 * B = step45 := by
  apply Subtype.ext
  decide +kernel

private def step46 : SL := ⟨!![z + 1, z, z; 0, 0, z; 1, z, z + 1], by decide +kernel⟩

private theorem step46_eq : step45 * inverseA = step46 := by
  apply Subtype.ext
  decide +kernel

private def step47 : SL := ⟨!![z + 1, 0, z; z + 1, 0, 0; z, 1, 1], by decide +kernel⟩

private theorem step47_eq : step46 * inverseB = step47 := by
  apply Subtype.ext
  decide +kernel

private def step48 : SL := ⟨!![1, z + 1, z + 1; z + 1, z + 1, z + 1; z + 1, 0, 1], by decide +kernel⟩

private theorem step48_eq : step47 * A = step48 := by
  apply Subtype.ext
  decide +kernel

private def step49 : SL := ⟨!![z + 1, 1, z; z + 1, 1, z + 1; z, 1, z], by decide +kernel⟩

private theorem step49_eq : step48 * B = step49 := by
  apply Subtype.ext
  decide +kernel

private def step50 : SL := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩

private theorem step50_eq : step49 * A = step50 := by
  apply Subtype.ext
  decide +kernel

theorem root01One_word : A * A * B⁻¹ * A⁻¹ * B * A⁻¹ * B * A⁻¹ * B⁻¹ * A * B * A = Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 := by

  rw [inv_A, inv_B]

  rw [step0_eq, step13_eq, step42_eq, step43_eq, step44_eq, step45_eq, step46_eq, step47_eq, step48_eq, step49_eq, step50_eq]

  apply Subtype.ext
  decide +kernel

private def step51 : SL := ⟨!![1, z, z; 1, z, 0; z, 0, 0], by decide +kernel⟩

private theorem step51_eq : step14 * A = step51 := by
  apply Subtype.ext
  decide +kernel

private def step52 : SL := ⟨!![0, 1, 1; z + 1, 1, 1; z + 1, 1, z + 1], by decide +kernel⟩

private theorem step52_eq : step51 * inverseB = step52 := by
  apply Subtype.ext
  decide +kernel

private def step53 : SL := ⟨!![1, 0, 1; 1, 0, z; z, z, 1], by decide +kernel⟩

private theorem step53_eq : step52 * inverseA = step53 := by
  apply Subtype.ext
  decide +kernel

private def step54 : SL := ⟨!![z, 1, z + 1; z + 1, z, z; z + 1, z + 1, 1], by decide +kernel⟩

private theorem step54_eq : step53 * inverseA = step54 := by
  apply Subtype.ext
  decide +kernel

private def step55 : SL := ⟨!![z, 0, z + 1; z, z + 1, 1; 0, z + 1, z + 1], by decide +kernel⟩

private theorem step55_eq : step54 * B = step55 := by
  apply Subtype.ext
  decide +kernel

private def step56 : SL := ⟨!![1, z + 1, 1; 0, z + 1, 0; z + 1, 1, 1], by decide +kernel⟩

private theorem step56_eq : step55 * B = step56 := by
  apply Subtype.ext
  decide +kernel

private def step57 : SL := ⟨!![0, 0, z + 1; 0, 1, z; z, 1, 0], by decide +kernel⟩

private theorem step57_eq : step56 * A = step57 := by
  apply Subtype.ext
  decide +kernel

private def step58 : SL := ⟨!![1, 0, 0; 0, 1, z; 0, 0, 1], by decide +kernel⟩

private theorem step58_eq : step57 * inverseB = step58 := by
  apply Subtype.ext
  decide +kernel

theorem root12Z_word : A * A * B⁻¹ * B⁻¹ * A * B⁻¹ * A⁻¹ * A⁻¹ * B * B * A * B⁻¹ = Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) z := by

  rw [inv_A, inv_B]

  rw [step0_eq, step13_eq, step14_eq, step51_eq, step52_eq, step53_eq, step54_eq, step55_eq, step56_eq, step57_eq, step58_eq]

  apply Subtype.ext
  decide +kernel

private def step59 : SL := ⟨!![1, z, z; 0, 1, 0; 1, 1, z + 1], by decide +kernel⟩

private theorem step59_eq : step24 * inverseA = step59 := by
  apply Subtype.ext
  decide +kernel

private def step60 : SL := ⟨!![z, 0, z + 1; z + 1, 1, z + 1; z, z, z + 1], by decide +kernel⟩

private theorem step60_eq : step59 * inverseA = step60 := by
  apply Subtype.ext
  decide +kernel

private def step61 : SL := ⟨!![1, z + 1, 1; z, 0, 0; 0, z, z], by decide +kernel⟩

private theorem step61_eq : step60 * B = step61 := by
  apply Subtype.ext
  decide +kernel

private def step62 : SL := ⟨!![0, z, 1; 0, 0, z; z, 0, z], by decide +kernel⟩

private theorem step62_eq : step61 * inverseA = step62 := by
  apply Subtype.ext
  decide +kernel

private def step63 : SL := ⟨!![z + 1, z + 1, z + 1; z + 1, z, z + 1; z + 1, z, 1], by decide +kernel⟩

private theorem step63_eq : step62 * inverseA = step63 := by
  apply Subtype.ext
  decide +kernel

private def step64 : SL := ⟨!![z, 1, 0; 1, 0, z; z, 0, z], by decide +kernel⟩

private theorem step64_eq : step63 * inverseB = step64 := by
  apply Subtype.ext
  decide +kernel

private def step65 : SL := ⟨!![z, 0, 1; z + 1, 1, 1; 0, z, z], by decide +kernel⟩

private theorem step65_eq : step64 * A = step65 := by
  apply Subtype.ext
  decide +kernel

private def step66 : SL := ⟨!![1, 1, z + 1; 0, z + 1, z + 1; z, z, z + 1], by decide +kernel⟩

private theorem step66_eq : step65 * inverseB = step66 := by
  apply Subtype.ext
  decide +kernel

private def step67 : SL := ⟨!![z, z + 1, z; z + 1, 1, z; 1, 1, z + 1], by decide +kernel⟩

private theorem step67_eq : step66 * A = step67 := by
  apply Subtype.ext
  decide +kernel

private def step68 : SL := ⟨!![1, 0, 0; 0, 1, 0; z, 0, 1], by decide +kernel⟩

private theorem step68_eq : step67 * B = step68 := by
  apply Subtype.ext
  decide +kernel

theorem root20Z_word : A * B⁻¹ * A⁻¹ * A⁻¹ * B * A⁻¹ * A⁻¹ * B⁻¹ * A * B⁻¹ * A * B = Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) z := by

  rw [inv_A, inv_B]

  rw [step24_eq, step59_eq, step60_eq, step61_eq, step62_eq, step63_eq, step64_eq, step65_eq, step66_eq, step67_eq, step68_eq]

  apply Subtype.ext
  decide +kernel

private def step69 : SL := ⟨!![1, 0, 1; 0, z + 1, z + 1; 1, z, 1], by decide +kernel⟩

private theorem step69_eq : step0 * B = step69 := by
  apply Subtype.ext
  decide +kernel

private def step70 : SL := ⟨!![z, 1, z + 1; z + 1, 0, z + 1; z + 1, z + 1, z], by decide +kernel⟩

private theorem step70_eq : step69 * inverseA = step70 := by
  apply Subtype.ext
  decide +kernel

private def step71 : SL := ⟨!![1, 0, 1; 0, z, 1; 0, 1, 0], by decide +kernel⟩

private theorem step71_eq : step70 * inverseB = step71 := by
  apply Subtype.ext
  decide +kernel

private def step72 : SL := ⟨!![0, 1, 1; 1, z + 1, 1; 0, z, z + 1], by decide +kernel⟩

private theorem step72_eq : step71 * A = step72 := by
  apply Subtype.ext
  decide +kernel

private def step73 : SL := ⟨!![1, 1, z; z, 0, z + 1; 0, z, z + 1], by decide +kernel⟩

private theorem step73_eq : step72 * inverseB = step73 := by
  apply Subtype.ext
  decide +kernel

private def step74 : SL := ⟨!![z, z, 0; z, 1, z + 1; 0, z, z + 1], by decide +kernel⟩

private theorem step74_eq : step73 * inverseB = step74 := by
  apply Subtype.ext
  decide +kernel

private def step75 : SL := ⟨!![z, 1, z + 1; 1, 0, 1; z + 1, z + 1, 1], by decide +kernel⟩

private theorem step75_eq : step74 * A = step75 := by
  apply Subtype.ext
  decide +kernel

private def step76 : SL := ⟨!![z, 0, z + 1; z, 1, z + 1; 0, z + 1, z + 1], by decide +kernel⟩

private theorem step76_eq : step75 * B = step76 := by
  apply Subtype.ext
  decide +kernel

private def step77 : SL := ⟨!![1, z + 1, 1; z, 0, z + 1; z + 1, 1, 1], by decide +kernel⟩

private theorem step77_eq : step76 * B = step77 := by
  apply Subtype.ext
  decide +kernel

private def step78 : SL := ⟨!![0, 0, z + 1; 1, z, z; z, 1, 0], by decide +kernel⟩

private theorem step78_eq : step77 * A = step78 := by
  apply Subtype.ext
  decide +kernel

private def step79 : SL := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide +kernel⟩

private theorem step79_eq : step78 * inverseB = step79 := by
  apply Subtype.ext
  decide +kernel

theorem root12One_word : A * A * B * A⁻¹ * B⁻¹ * A * B⁻¹ * B⁻¹ * A * B * B * A * B⁻¹ = Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 := by

  rw [inv_A, inv_B]

  rw [step0_eq, step69_eq, step70_eq, step71_eq, step72_eq, step73_eq, step74_eq, step75_eq, step76_eq, step77_eq, step78_eq, step79_eq]

  apply Subtype.ext
  decide +kernel

theorem z_sq : z ^ 2 = z + 1 := by decide +kernel

theorem A_fifth : A ^ 5 = 1 := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one] using fifthA_word

theorem B_fifth : B ^ 5 = 1 := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one] using fifthB_word

theorem AB_cube : (A * B) ^ 3 = 1 := by
  simpa only [pow_succ, pow_zero, one_mul, mul_one, ← mul_assoc] using cubeAB_word

private theorem mixed_expansion {G : Type*} [Group G] (x y : G) :
    x ^ 2 * (y ^ 2)⁻¹ * x⁻¹ * y⁻¹ * x * (y ^ 2)⁻¹ * x * y * x⁻¹ * y⁻¹ =
      x * x * y⁻¹ * y⁻¹ * x⁻¹ * y⁻¹ * x * y⁻¹ * y⁻¹ * x * y * x⁻¹ * y⁻¹ := by
  simp only [pow_two, _root_.mul_inv_rev, ← mul_assoc]

theorem mixed_scalar :
    A ^ 2 * (B ^ 2)⁻¹ * A⁻¹ * B⁻¹ * A * (B ^ 2)⁻¹ * A * B * A⁻¹ * B⁻¹ = scalarZ := by
  exact (mixed_expansion A B).trans mixedAB_word

theorem scalarZ_mem_center : scalarZ ∈ Subgroup.center SL := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  exact ⟨z, by decide +kernel, by decide +kernel⟩


end Matrix.PSL3.ExceptionalFourCover.TwoGeneratorPresentation.MatrixMarking
