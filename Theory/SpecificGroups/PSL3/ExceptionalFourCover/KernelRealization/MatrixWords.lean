module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Checked matrix words generating SL₃(4)

Positive words in the actual matrix coordinates recover a coordinate cycle
and x₀₁(1), x₀₁(z). Each step is a separate multiplication of explicit matrices,
so kernel checking does not expand a long nested product. `Source/matrix_words.py`
reproduces the search and the proof chains. No search result is trusted by Lean.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel
open Matrix.SpecialLinearGroup

def cycle : SL := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide +kernel⟩

private def cycleStep0 : SL := ⟨!![1, 0, 1; 0, z + 1, z; z + 1, 1, z], by decide +kernel⟩
private theorem cycleStep0_eq : (1 : SL) * matrixY = cycleStep0 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep1 : SL := ⟨!![z, 1, z + 1; 1, 0, z; z, 1, z], by decide +kernel⟩
private theorem cycleStep1_eq : cycleStep0 * matrixY = cycleStep1 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep2 : SL := ⟨!![z, z + 1, 0; z + 1, 1, 1; z, 0, 0], by decide +kernel⟩
private theorem cycleStep2_eq : cycleStep1 * matrixX = cycleStep2 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep3 : SL := ⟨!![z + 1, z + 1, z + 1; 1, z, 1; 1, 0, z], by decide +kernel⟩
private theorem cycleStep3_eq : cycleStep2 * matrixX = cycleStep3 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep4 : SL := ⟨!![1, 1, z + 1; z, 0, 0; 0, z, z], by decide +kernel⟩
private theorem cycleStep4_eq : cycleStep3 * matrixY = cycleStep4 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep5 : SL := ⟨!![z + 1, 0, z; z, 0, z; 1, z + 1, 0], by decide +kernel⟩
private theorem cycleStep5_eq : cycleStep4 * matrixY = cycleStep5 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep6 : SL := ⟨!![z, 1, z + 1; 1, 1, z; 1, z + 1, 0], by decide +kernel⟩
private theorem cycleStep6_eq : cycleStep5 * matrixX = cycleStep6 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep7 : SL := ⟨!![0, 0, 1; 0, 1, 0; 1, z, 0], by decide +kernel⟩
private theorem cycleStep7_eq : cycleStep6 * matrixY = cycleStep7 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep8 : SL := ⟨!![z + 1, 1, z; 0, z + 1, z; 1, 1, z], by decide +kernel⟩
private theorem cycleStep8_eq : cycleStep7 * matrixY = cycleStep8 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep9 : SL := ⟨!![z, 1, z; 1, 0, z; 0, 1, 0], by decide +kernel⟩
private theorem cycleStep9_eq : cycleStep8 * matrixY = cycleStep9 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep10 : SL := ⟨!![z + 1, 1, z + 1; 0, z, z; 0, z + 1, z], by decide +kernel⟩
private theorem cycleStep10_eq : cycleStep9 * matrixY = cycleStep10 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep11 : SL := ⟨!![1, z + 1, 1; 1, z + 1, z + 1; z, z, 1], by decide +kernel⟩
private theorem cycleStep11_eq : cycleStep10 * matrixX = cycleStep11 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep12 : SL := ⟨!![z, z + 1, z; z + 1, 1, 1; 1, 0, z + 1], by decide +kernel⟩
private theorem cycleStep12_eq : cycleStep11 * matrixY = cycleStep12 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep13 : SL := ⟨!![z + 1, z, z + 1; 1, z, 1; z + 1, z, 1], by decide +kernel⟩
private theorem cycleStep13_eq : cycleStep12 * matrixX = cycleStep13 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep14 : SL := ⟨!![z + 1, 0, 0; z, 1, z; z + 1, 1, 0], by decide +kernel⟩
private theorem cycleStep14_eq : cycleStep13 * matrixX = cycleStep14 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep15 : SL := ⟨!![z + 1, 0, z + 1; z + 1, 1, z + 1; z + 1, z + 1, 1], by decide +kernel⟩
private theorem cycleStep15_eq : cycleStep14 * matrixY = cycleStep15 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep16 : SL := ⟨!![z, z, z + 1; 1, z + 1, 1; 0, 0, z], by decide +kernel⟩
private theorem cycleStep16_eq : cycleStep15 * matrixX = cycleStep16 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep17 : SL := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide +kernel⟩
private theorem cycleStep17_eq : cycleStep16 * matrixX = cycleStep17 := by
  apply Subtype.ext
  decide +kernel

theorem cycle_mem (K : Subgroup SL) (hX : matrixX ∈ K) (hY : matrixY ∈ K) :
    cycle ∈ K := by
  have h0 : cycleStep0 ∈ K := by
    rw [← cycleStep0_eq]
    exact K.mul_mem K.one_mem hY
  have h1 : cycleStep1 ∈ K := by
    rw [← cycleStep1_eq]
    exact K.mul_mem h0 hY
  have h2 : cycleStep2 ∈ K := by
    rw [← cycleStep2_eq]
    exact K.mul_mem h1 hX
  have h3 : cycleStep3 ∈ K := by
    rw [← cycleStep3_eq]
    exact K.mul_mem h2 hX
  have h4 : cycleStep4 ∈ K := by
    rw [← cycleStep4_eq]
    exact K.mul_mem h3 hY
  have h5 : cycleStep5 ∈ K := by
    rw [← cycleStep5_eq]
    exact K.mul_mem h4 hY
  have h6 : cycleStep6 ∈ K := by
    rw [← cycleStep6_eq]
    exact K.mul_mem h5 hX
  have h7 : cycleStep7 ∈ K := by
    rw [← cycleStep7_eq]
    exact K.mul_mem h6 hY
  have h8 : cycleStep8 ∈ K := by
    rw [← cycleStep8_eq]
    exact K.mul_mem h7 hY
  have h9 : cycleStep9 ∈ K := by
    rw [← cycleStep9_eq]
    exact K.mul_mem h8 hY
  have h10 : cycleStep10 ∈ K := by
    rw [← cycleStep10_eq]
    exact K.mul_mem h9 hY
  have h11 : cycleStep11 ∈ K := by
    rw [← cycleStep11_eq]
    exact K.mul_mem h10 hX
  have h12 : cycleStep12 ∈ K := by
    rw [← cycleStep12_eq]
    exact K.mul_mem h11 hY
  have h13 : cycleStep13 ∈ K := by
    rw [← cycleStep13_eq]
    exact K.mul_mem h12 hX
  have h14 : cycleStep14 ∈ K := by
    rw [← cycleStep14_eq]
    exact K.mul_mem h13 hX
  have h15 : cycleStep15 ∈ K := by
    rw [← cycleStep15_eq]
    exact K.mul_mem h14 hY
  have h16 : cycleStep16 ∈ K := by
    rw [← cycleStep16_eq]
    exact K.mul_mem h15 hX
  have h17 : cycleStep17 ∈ K := by
    rw [← cycleStep17_eq]
    exact K.mul_mem h16 hX
  have he : cycleStep17 = cycle := by
    apply Subtype.ext
    decide +kernel
  exact he ▸ h17

def rootOne : SL := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1

private def rootOneStep0 : SL := ⟨!![z + 1, 0, 1; z + 1, 1, z; 0, z + 1, 0], by decide +kernel⟩
private theorem rootOneStep0_eq : (1 : SL) * matrixX = rootOneStep0 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep1 : SL := ⟨!![0, 1, 1; z, 1, z; 0, z, 1], by decide +kernel⟩
private theorem rootOneStep1_eq : rootOneStep0 * matrixY = rootOneStep1 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep2 : SL := ⟨!![z + 1, z, 0; z + 1, 1, z + 1; z + 1, 0, 1], by decide +kernel⟩
private theorem rootOneStep2_eq : rootOneStep1 * matrixY = rootOneStep2 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep3 : SL := ⟨!![z + 1, z, 0; 1, z + 1, 1; z, z + 1, z + 1], by decide +kernel⟩
private theorem rootOneStep3_eq : rootOneStep2 * matrixX = rootOneStep3 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep4 : SL := ⟨!![z + 1, z, 0; 1, 0, 0; z + 1, 1, z + 1], by decide +kernel⟩
private theorem rootOneStep4_eq : rootOneStep3 * matrixX = rootOneStep4 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep5 : SL := ⟨!![z + 1, 1, 0; 1, 0, 1; 1, 0, 0], by decide +kernel⟩
private theorem rootOneStep5_eq : rootOneStep4 * matrixY = rootOneStep5 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep6 : SL := ⟨!![1, 1, 1; z + 1, z + 1, 1; z + 1, 0, 1], by decide +kernel⟩
private theorem rootOneStep6_eq : rootOneStep5 * matrixX = rootOneStep6 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep7 : SL := ⟨!![0, z, z + 1; 0, 0, z; z, z + 1, z + 1], by decide +kernel⟩
private theorem rootOneStep7_eq : rootOneStep6 * matrixX = rootOneStep7 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep8 : SL := ⟨!![z, z, z; 1, z, z + 1; 0, 1, z], by decide +kernel⟩
private theorem rootOneStep8_eq : rootOneStep7 * matrixY = rootOneStep8 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep9 : SL := ⟨!![0, z + 1, 1; z, 0, z; z + 1, 0, z], by decide +kernel⟩
private theorem rootOneStep9_eq : rootOneStep8 * matrixX = rootOneStep9 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep10 : SL := ⟨!![z, 0, 1; 1, 1, z; z, 1, z + 1], by decide +kernel⟩
private theorem rootOneStep10_eq : rootOneStep9 * matrixX = rootOneStep10 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep11 : SL := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩
private theorem rootOneStep11_eq : rootOneStep10 * matrixY = rootOneStep11 := by
  apply Subtype.ext
  decide +kernel

theorem rootOne_mem (K : Subgroup SL) (hX : matrixX ∈ K) (hY : matrixY ∈ K) :
    rootOne ∈ K := by
  have h0 : rootOneStep0 ∈ K := by
    rw [← rootOneStep0_eq]
    exact K.mul_mem K.one_mem hX
  have h1 : rootOneStep1 ∈ K := by
    rw [← rootOneStep1_eq]
    exact K.mul_mem h0 hY
  have h2 : rootOneStep2 ∈ K := by
    rw [← rootOneStep2_eq]
    exact K.mul_mem h1 hY
  have h3 : rootOneStep3 ∈ K := by
    rw [← rootOneStep3_eq]
    exact K.mul_mem h2 hX
  have h4 : rootOneStep4 ∈ K := by
    rw [← rootOneStep4_eq]
    exact K.mul_mem h3 hX
  have h5 : rootOneStep5 ∈ K := by
    rw [← rootOneStep5_eq]
    exact K.mul_mem h4 hY
  have h6 : rootOneStep6 ∈ K := by
    rw [← rootOneStep6_eq]
    exact K.mul_mem h5 hX
  have h7 : rootOneStep7 ∈ K := by
    rw [← rootOneStep7_eq]
    exact K.mul_mem h6 hX
  have h8 : rootOneStep8 ∈ K := by
    rw [← rootOneStep8_eq]
    exact K.mul_mem h7 hY
  have h9 : rootOneStep9 ∈ K := by
    rw [← rootOneStep9_eq]
    exact K.mul_mem h8 hX
  have h10 : rootOneStep10 ∈ K := by
    rw [← rootOneStep10_eq]
    exact K.mul_mem h9 hX
  have h11 : rootOneStep11 ∈ K := by
    rw [← rootOneStep11_eq]
    exact K.mul_mem h10 hY
  have he : rootOneStep11 = rootOne := by
    apply Subtype.ext
    decide +kernel
  exact he ▸ h11

def rootZ : SL := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) z

private def rootZStep0 : SL := ⟨!![z + 1, 0, 1; z + 1, 1, z; 0, z + 1, 0], by decide +kernel⟩
private theorem rootZStep0_eq : (1 : SL) * matrixX = rootZStep0 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep1 : SL := ⟨!![0, 1, 1; z, 1, z; 0, z, 1], by decide +kernel⟩
private theorem rootZStep1_eq : rootZStep0 * matrixY = rootZStep1 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep2 : SL := ⟨!![z + 1, z, 0; z + 1, 1, z + 1; z + 1, 0, 1], by decide +kernel⟩
private theorem rootZStep2_eq : rootZStep1 * matrixY = rootZStep2 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep3 : SL := ⟨!![z + 1, z, 0; 1, z + 1, 1; z, z + 1, z + 1], by decide +kernel⟩
private theorem rootZStep3_eq : rootZStep2 * matrixX = rootZStep3 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep4 : SL := ⟨!![z + 1, 1, 0; z, z + 1, z; 0, 1, z], by decide +kernel⟩
private theorem rootZStep4_eq : rootZStep3 * matrixY = rootZStep4 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep5 : SL := ⟨!![1, 1, 1; z + 1, z, z + 1; z + 1, 0, z], by decide +kernel⟩
private theorem rootZStep5_eq : rootZStep4 * matrixX = rootZStep5 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep6 : SL := ⟨!![0, z, z + 1; z + 1, 0, 0; z, 1, z + 1], by decide +kernel⟩
private theorem rootZStep6_eq : rootZStep5 * matrixX = rootZStep6 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep7 : SL := ⟨!![z, z, z; z + 1, 0, z + 1; 0, 0, 1], by decide +kernel⟩
private theorem rootZStep7_eq : rootZStep6 * matrixY = rootZStep7 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep8 : SL := ⟨!![z + 1, z + 1, z; 1, z + 1, z; z + 1, 1, z], by decide +kernel⟩
private theorem rootZStep8_eq : rootZStep7 * matrixY = rootZStep8 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep9 : SL := ⟨!![0, z, z; 1, z, 0; 1, 0, 1], by decide +kernel⟩
private theorem rootZStep9_eq : rootZStep8 * matrixX = rootZStep9 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep10 : SL := ⟨!![1, z + 1, 0; 1, 1, z; z, 1, z + 1], by decide +kernel⟩
private theorem rootZStep10_eq : rootZStep9 * matrixY = rootZStep10 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep11 : SL := ⟨!![1, z, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩
private theorem rootZStep11_eq : rootZStep10 * matrixY = rootZStep11 := by
  apply Subtype.ext
  decide +kernel

theorem rootZ_mem (K : Subgroup SL) (hX : matrixX ∈ K) (hY : matrixY ∈ K) :
    rootZ ∈ K := by
  have h0 : rootZStep0 ∈ K := by
    rw [← rootZStep0_eq]
    exact K.mul_mem K.one_mem hX
  have h1 : rootZStep1 ∈ K := by
    rw [← rootZStep1_eq]
    exact K.mul_mem h0 hY
  have h2 : rootZStep2 ∈ K := by
    rw [← rootZStep2_eq]
    exact K.mul_mem h1 hY
  have h3 : rootZStep3 ∈ K := by
    rw [← rootZStep3_eq]
    exact K.mul_mem h2 hX
  have h4 : rootZStep4 ∈ K := by
    rw [← rootZStep4_eq]
    exact K.mul_mem h3 hY
  have h5 : rootZStep5 ∈ K := by
    rw [← rootZStep5_eq]
    exact K.mul_mem h4 hX
  have h6 : rootZStep6 ∈ K := by
    rw [← rootZStep6_eq]
    exact K.mul_mem h5 hX
  have h7 : rootZStep7 ∈ K := by
    rw [← rootZStep7_eq]
    exact K.mul_mem h6 hY
  have h8 : rootZStep8 ∈ K := by
    rw [← rootZStep8_eq]
    exact K.mul_mem h7 hY
  have h9 : rootZStep9 ∈ K := by
    rw [← rootZStep9_eq]
    exact K.mul_mem h8 hX
  have h10 : rootZStep10 ∈ K := by
    rw [← rootZStep10_eq]
    exact K.mul_mem h9 hY
  have h11 : rootZStep11 ∈ K := by
    rw [← rootZStep11_eq]
    exact K.mul_mem h10 hY
  have he : rootZStep11 = rootZ := by
    apply Subtype.ext
    decide +kernel
  exact he ▸ h11

end Matrix.PSL3.ExceptionalFourCover.KernelModel
