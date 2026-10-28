module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.ProjectiveComparison.Coordinates
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
/-!
# Short matrix words for elementary generators

The checked multiplication chains express a coordinate cycle and the two
root elements x₀₁(1), x₀₁(z) as positive words in `matrixA` and `matrixB`.
Each step multiplies two explicit 3-by-3 matrices; the kernel never expands
a long nested matrix product. Together with the root commutator identities,
these three elements generate SL₃(4).

The words were found by a breadth-first search over the explicit quadratic
field, but only the individual Lean equalities are used in the proof.
Input matrices and conventions are documented in `Coordinates`; the
reproducible word data and generator are retained in `Source`.
-/

@[expose] public section

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison
open Matrix.SpecialLinearGroup

def cycle : SL := ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide +kernel⟩

private def cycleStep0 : SL := ⟨![![z, 0, z + 1], ![z, 0, 1], ![z, z, z]], by decide +kernel⟩
private theorem cycleStep0_eq : (1 : SL) * matrixA = cycleStep0 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep1 : SL := ⟨![![z, 0, 1], ![0, 0, z + 1], ![1, 1, 1]], by decide +kernel⟩
private theorem cycleStep1_eq : cycleStep0 * matrixB = cycleStep1 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep2 : SL := ⟨![![0, 0, z + 1], ![z + 1, 0, z + 1], ![z + 1, z + 1, z + 1]], by decide +kernel⟩
private theorem cycleStep2_eq : cycleStep1 * matrixB = cycleStep2 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep3 : SL := ⟨![![1, 1, 1], ![0, 1, z + 1], ![1, 1, 0]], by decide +kernel⟩
private theorem cycleStep3_eq : cycleStep2 * matrixA = cycleStep3 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep4 : SL := ⟨![![z + 1, z + 1, z + 1], ![z, z + 1, 0], ![z, z + 1, z]], by decide +kernel⟩
private theorem cycleStep4_eq : cycleStep3 * matrixB = cycleStep4 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep5 : SL := ⟨![![1, 1, 0], ![z, 0, z], ![1, z + 1, 1]], by decide +kernel⟩
private theorem cycleStep5_eq : cycleStep4 * matrixA = cycleStep5 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep6 : SL := ⟨![![0, 0, z], ![0, z + 1, z], ![1, z, z]], by decide +kernel⟩
private theorem cycleStep6_eq : cycleStep5 * matrixA = cycleStep6 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep7 : SL := ⟨![![z, 0, z], ![1, z, 0], ![z + 1, 1, z]], by decide +kernel⟩
private theorem cycleStep7_eq : cycleStep6 * matrixB = cycleStep7 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep8 : SL := ⟨![![0, z + 1, z], ![1, 0, 1], ![0, z + 1, 0]], by decide +kernel⟩
private theorem cycleStep8_eq : cycleStep7 * matrixA = cycleStep8 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep9 : SL := ⟨![![1, z, 0], ![z, 0, 0], ![z + 1, z, z]], by decide +kernel⟩
private theorem cycleStep9_eq : cycleStep8 * matrixB = cycleStep9 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep10 : SL := ⟨![![1, 1, 0], ![1, 0, z], ![z, 1, 0]], by decide +kernel⟩
private theorem cycleStep10_eq : cycleStep9 * matrixB = cycleStep10 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep11 : SL := ⟨![![0, 0, z], ![1, z + 1, 0], ![1, 0, 0]], by decide +kernel⟩
private theorem cycleStep11_eq : cycleStep10 * matrixA = cycleStep11 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep12 : SL := ⟨![![z + 1, z + 1, z + 1], ![z + 1, 0, 0], ![z, 0, z + 1]], by decide +kernel⟩
private theorem cycleStep12_eq : cycleStep11 * matrixA = cycleStep12 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep13 : SL := ⟨![![z, z, z], ![z, 0, z + 1], ![z, 0, 1]], by decide +kernel⟩
private theorem cycleStep13_eq : cycleStep12 * matrixB = cycleStep13 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep14 : SL := ⟨![![z + 1, z + 1, 0], ![z, 1, 0], ![1, z, z + 1]], by decide +kernel⟩
private theorem cycleStep14_eq : cycleStep13 * matrixA = cycleStep14 := by
  apply Subtype.ext
  decide +kernel

private def cycleStep15 : SL := ⟨![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]], by decide +kernel⟩
private theorem cycleStep15_eq : cycleStep14 * matrixA = cycleStep15 := by
  apply Subtype.ext
  decide +kernel

theorem cycle_mem (K : Subgroup SL) (hA : matrixA ∈ K) (hB : matrixB ∈ K) :
    cycle ∈ K := by
  have h0 : cycleStep0 ∈ K := cycleStep0_eq ▸ K.mul_mem K.one_mem hA
  have h1 : cycleStep1 ∈ K := cycleStep1_eq ▸ K.mul_mem h0 hB
  have h2 : cycleStep2 ∈ K := cycleStep2_eq ▸ K.mul_mem h1 hB
  have h3 : cycleStep3 ∈ K := cycleStep3_eq ▸ K.mul_mem h2 hA
  have h4 : cycleStep4 ∈ K := cycleStep4_eq ▸ K.mul_mem h3 hB
  have h5 : cycleStep5 ∈ K := cycleStep5_eq ▸ K.mul_mem h4 hA
  have h6 : cycleStep6 ∈ K := cycleStep6_eq ▸ K.mul_mem h5 hA
  have h7 : cycleStep7 ∈ K := cycleStep7_eq ▸ K.mul_mem h6 hB
  have h8 : cycleStep8 ∈ K := cycleStep8_eq ▸ K.mul_mem h7 hA
  have h9 : cycleStep9 ∈ K := cycleStep9_eq ▸ K.mul_mem h8 hB
  have h10 : cycleStep10 ∈ K := cycleStep10_eq ▸ K.mul_mem h9 hB
  have h11 : cycleStep11 ∈ K := cycleStep11_eq ▸ K.mul_mem h10 hA
  have h12 : cycleStep12 ∈ K := cycleStep12_eq ▸ K.mul_mem h11 hA
  have h13 : cycleStep13 ∈ K := cycleStep13_eq ▸ K.mul_mem h12 hB
  have h14 : cycleStep14 ∈ K := cycleStep14_eq ▸ K.mul_mem h13 hA
  have h15 : cycleStep15 ∈ K := cycleStep15_eq ▸ K.mul_mem h14 hA
  have he : cycleStep15 = cycle := by
    apply Subtype.ext
    decide +kernel
  exact he ▸ h15

private def rootOneStep0 : SL := ⟨![![z, 0, z + 1], ![z, 0, 1], ![z, z, z]], by decide +kernel⟩
private theorem rootOneStep0_eq : (1 : SL) * matrixA = rootOneStep0 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep1 : SL := ⟨![![z, 1, 0], ![1, z, z + 1], ![z + 1, z + 1, 0]], by decide +kernel⟩
private theorem rootOneStep1_eq : rootOneStep0 * matrixA = rootOneStep1 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep2 : SL := ⟨![![0, z + 1, 1], ![z, 1, z + 1], ![1, z, 1]], by decide +kernel⟩
private theorem rootOneStep2_eq : rootOneStep1 * matrixB = rootOneStep2 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep3 : SL := ⟨![![z + 1, z, 1], ![0, 1, 1], ![z + 1, z, z + 1]], by decide +kernel⟩
private theorem rootOneStep3_eq : rootOneStep2 * matrixA = rootOneStep3 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep4 : SL := ⟨![![0, z, z], ![0, z, z + 1], ![z + 1, 1, 1]], by decide +kernel⟩
private theorem rootOneStep4_eq : rootOneStep3 * matrixA = rootOneStep4 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep5 : SL := ⟨![![0, 1, z + 1], ![1, 1, z], ![z, z + 1, 1]], by decide +kernel⟩
private theorem rootOneStep5_eq : rootOneStep4 * matrixB = rootOneStep5 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep6 : SL := ⟨![![z, z + 1, 0], ![0, z + 1, 0], ![z + 1, z, 1]], by decide +kernel⟩
private theorem rootOneStep6_eq : rootOneStep5 * matrixB = rootOneStep6 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep7 : SL := ⟨![![z, z, 0], ![z + 1, z, z], ![1, 1, z + 1]], by decide +kernel⟩
private theorem rootOneStep7_eq : rootOneStep6 * matrixB = rootOneStep7 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep8 : SL := ⟨![![0, 0, z + 1], ![1, z + 1, z + 1], ![1, 1, z + 1]], by decide +kernel⟩
private theorem rootOneStep8_eq : rootOneStep7 * matrixA = rootOneStep8 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep9 : SL := ⟨![![z + 1, 0, z + 1], ![z + 1, z, 0], ![1, z + 1, 1]], by decide +kernel⟩
private theorem rootOneStep9_eq : rootOneStep8 * matrixB = rootOneStep9 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep10 : SL := ⟨![![1, 0, 0], ![0, 1, z], ![1, z, z]], by decide +kernel⟩
private theorem rootOneStep10_eq : rootOneStep9 * matrixB = rootOneStep10 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep11 : SL := ⟨![![z, 0, z + 1], ![1, z + 1, z], ![z, z + 1, z]], by decide +kernel⟩
private theorem rootOneStep11_eq : rootOneStep10 * matrixA = rootOneStep11 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep12 : SL := ⟨![![z, 0, 1], ![z, z, 1], ![0, z, z]], by decide +kernel⟩
private theorem rootOneStep12_eq : rootOneStep11 * matrixB = rootOneStep12 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep13 : SL := ⟨![![0, 0, z + 1], ![z, 1, z], ![0, 1, z + 1]], by decide +kernel⟩
private theorem rootOneStep13_eq : rootOneStep12 * matrixB = rootOneStep13 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep14 : SL := ⟨![![1, 1, 1], ![z, z + 1, z + 1], ![z + 1, 1, 0]], by decide +kernel⟩
private theorem rootOneStep14_eq : rootOneStep13 * matrixA = rootOneStep14 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep15 : SL := ⟨![![z + 1, z + 1, z + 1], ![1, z, z + 1], ![z + 1, z + 1, 0]], by decide +kernel⟩
private theorem rootOneStep15_eq : rootOneStep14 * matrixB = rootOneStep15 := by
  apply Subtype.ext
  decide +kernel

private def rootOneStep16 : SL := ⟨![![1, 1, 0], ![0, 1, 0], ![0, 0, 1]], by decide +kernel⟩
private theorem rootOneStep16_eq : rootOneStep15 * matrixA = rootOneStep16 := by
  apply Subtype.ext
  decide +kernel

theorem rootOne_mem (K : Subgroup SL) (hA : matrixA ∈ K) (hB : matrixB ∈ K) :
    transvection (show (0 : Fin 3) ≠ 1 by decide) 1 ∈ K := by
  have h0 : rootOneStep0 ∈ K := rootOneStep0_eq ▸ K.mul_mem K.one_mem hA
  have h1 : rootOneStep1 ∈ K := rootOneStep1_eq ▸ K.mul_mem h0 hA
  have h2 : rootOneStep2 ∈ K := rootOneStep2_eq ▸ K.mul_mem h1 hB
  have h3 : rootOneStep3 ∈ K := rootOneStep3_eq ▸ K.mul_mem h2 hA
  have h4 : rootOneStep4 ∈ K := rootOneStep4_eq ▸ K.mul_mem h3 hA
  have h5 : rootOneStep5 ∈ K := rootOneStep5_eq ▸ K.mul_mem h4 hB
  have h6 : rootOneStep6 ∈ K := rootOneStep6_eq ▸ K.mul_mem h5 hB
  have h7 : rootOneStep7 ∈ K := rootOneStep7_eq ▸ K.mul_mem h6 hB
  have h8 : rootOneStep8 ∈ K := rootOneStep8_eq ▸ K.mul_mem h7 hA
  have h9 : rootOneStep9 ∈ K := rootOneStep9_eq ▸ K.mul_mem h8 hB
  have h10 : rootOneStep10 ∈ K := rootOneStep10_eq ▸ K.mul_mem h9 hB
  have h11 : rootOneStep11 ∈ K := rootOneStep11_eq ▸ K.mul_mem h10 hA
  have h12 : rootOneStep12 ∈ K := rootOneStep12_eq ▸ K.mul_mem h11 hB
  have h13 : rootOneStep13 ∈ K := rootOneStep13_eq ▸ K.mul_mem h12 hB
  have h14 : rootOneStep14 ∈ K := rootOneStep14_eq ▸ K.mul_mem h13 hA
  have h15 : rootOneStep15 ∈ K := rootOneStep15_eq ▸ K.mul_mem h14 hB
  have h16 : rootOneStep16 ∈ K := rootOneStep16_eq ▸ K.mul_mem h15 hA
  have he : rootOneStep16 = transvection (show (0 : Fin 3) ≠ 1 by decide) 1 := by
    apply Subtype.ext
    decide +kernel
  exact he ▸ h16

private def rootZStep0 : SL := ⟨![![z, 0, z + 1], ![z, 0, 1], ![z, z, z]], by decide +kernel⟩
private theorem rootZStep0_eq : (1 : SL) * matrixA = rootZStep0 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep1 : SL := ⟨![![z, 1, 0], ![1, z, z + 1], ![z + 1, z + 1, 0]], by decide +kernel⟩
private theorem rootZStep1_eq : rootZStep0 * matrixA = rootZStep1 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep2 : SL := ⟨![![0, z + 1, 1], ![z, 1, z + 1], ![1, z, 1]], by decide +kernel⟩
private theorem rootZStep2_eq : rootZStep1 * matrixB = rootZStep2 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep3 : SL := ⟨![![z + 1, z, 1], ![0, 1, 1], ![z + 1, z, z + 1]], by decide +kernel⟩
private theorem rootZStep3_eq : rootZStep2 * matrixA = rootZStep3 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep4 : SL := ⟨![![1, 1, z + 1], ![0, z + 1, z], ![z + 1, 1, 1]], by decide +kernel⟩
private theorem rootZStep4_eq : rootZStep3 * matrixB = rootZStep4 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep5 : SL := ⟨![![1, 1, z + 1], ![z, z + 1, 0], ![1, z, 1]], by decide +kernel⟩
private theorem rootZStep5_eq : rootZStep4 * matrixA = rootZStep5 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep6 : SL := ⟨![![1, 1, z + 1], ![z, 0, z], ![z + 1, z, z + 1]], by decide +kernel⟩
private theorem rootZStep6_eq : rootZStep5 * matrixA = rootZStep6 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep7 : SL := ⟨![![1, z + 1, 1], ![z + 1, 0, 0], ![z + 1, 1, 1]], by decide +kernel⟩
private theorem rootZStep7_eq : rootZStep6 * matrixB = rootZStep7 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep8 : SL := ⟨![![1, z, z], ![z, 0, z + 1], ![z, z + 1, 1]], by decide +kernel⟩
private theorem rootZStep8_eq : rootZStep7 * matrixB = rootZStep8 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep9 : SL := ⟨![![z + 1, 1, z], ![z, 0, 1], ![z + 1, z, 1]], by decide +kernel⟩
private theorem rootZStep9_eq : rootZStep8 * matrixB = rootZStep9 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep10 : SL := ⟨![![0, z + 1, 0], ![1, z, z + 1], ![0, z, z]], by decide +kernel⟩
private theorem rootZStep10_eq : rootZStep9 * matrixA = rootZStep10 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep11 : SL := ⟨![![z + 1, z, z], ![z, 1, z + 1], ![0, 1, z + 1]], by decide +kernel⟩
private theorem rootZStep11_eq : rootZStep10 * matrixB = rootZStep11 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep12 : SL := ⟨![![1, z + 1, z + 1], ![0, 1, 1], ![z + 1, 1, 0]], by decide +kernel⟩
private theorem rootZStep12_eq : rootZStep11 * matrixA = rootZStep12 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep13 : SL := ⟨![![z + 1, z, 0], ![0, z + 1, z], ![z + 1, z + 1, 0]], by decide +kernel⟩
private theorem rootZStep13_eq : rootZStep12 * matrixB = rootZStep13 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep14 : SL := ⟨![![z, 0, 0], ![z, z + 1, 0], ![0, 0, 1]], by decide +kernel⟩
private theorem rootZStep14_eq : rootZStep13 * matrixA = rootZStep14 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep15 : SL := ⟨![![z + 1, 0, 1], ![z, 0, z], ![z, z, z]], by decide +kernel⟩
private theorem rootZStep15_eq : rootZStep14 * matrixA = rootZStep15 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep16 : SL := ⟨![![z + 1, 0, z], ![z + 1, 0, 0], ![1, 1, 1]], by decide +kernel⟩
private theorem rootZStep16_eq : rootZStep15 * matrixB = rootZStep16 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep17 : SL := ⟨![![0, 0, 1], ![z, 0, z + 1], ![z + 1, z + 1, z + 1]], by decide +kernel⟩
private theorem rootZStep17_eq : rootZStep16 * matrixB = rootZStep17 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep18 : SL := ⟨![![1, 0, 1], ![z, 0, 1], ![z, z, z]], by decide +kernel⟩
private theorem rootZStep18_eq : rootZStep17 * matrixB = rootZStep18 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep19 : SL := ⟨![![0, z, 1], ![1, z, z + 1], ![z + 1, z + 1, 0]], by decide +kernel⟩
private theorem rootZStep19_eq : rootZStep18 * matrixA = rootZStep19 := by
  apply Subtype.ext
  decide +kernel

private def rootZStep20 : SL := ⟨![![1, z, 0], ![0, 1, 0], ![0, 0, 1]], by decide +kernel⟩
private theorem rootZStep20_eq : rootZStep19 * matrixA = rootZStep20 := by
  apply Subtype.ext
  decide +kernel

theorem rootZ_mem (K : Subgroup SL) (hA : matrixA ∈ K) (hB : matrixB ∈ K) :
    transvection (show (0 : Fin 3) ≠ 1 by decide) z ∈ K := by
  have h0 : rootZStep0 ∈ K := rootZStep0_eq ▸ K.mul_mem K.one_mem hA
  have h1 : rootZStep1 ∈ K := rootZStep1_eq ▸ K.mul_mem h0 hA
  have h2 : rootZStep2 ∈ K := rootZStep2_eq ▸ K.mul_mem h1 hB
  have h3 : rootZStep3 ∈ K := rootZStep3_eq ▸ K.mul_mem h2 hA
  have h4 : rootZStep4 ∈ K := rootZStep4_eq ▸ K.mul_mem h3 hB
  have h5 : rootZStep5 ∈ K := rootZStep5_eq ▸ K.mul_mem h4 hA
  have h6 : rootZStep6 ∈ K := rootZStep6_eq ▸ K.mul_mem h5 hA
  have h7 : rootZStep7 ∈ K := rootZStep7_eq ▸ K.mul_mem h6 hB
  have h8 : rootZStep8 ∈ K := rootZStep8_eq ▸ K.mul_mem h7 hB
  have h9 : rootZStep9 ∈ K := rootZStep9_eq ▸ K.mul_mem h8 hB
  have h10 : rootZStep10 ∈ K := rootZStep10_eq ▸ K.mul_mem h9 hA
  have h11 : rootZStep11 ∈ K := rootZStep11_eq ▸ K.mul_mem h10 hB
  have h12 : rootZStep12 ∈ K := rootZStep12_eq ▸ K.mul_mem h11 hA
  have h13 : rootZStep13 ∈ K := rootZStep13_eq ▸ K.mul_mem h12 hB
  have h14 : rootZStep14 ∈ K := rootZStep14_eq ▸ K.mul_mem h13 hA
  have h15 : rootZStep15 ∈ K := rootZStep15_eq ▸ K.mul_mem h14 hA
  have h16 : rootZStep16 ∈ K := rootZStep16_eq ▸ K.mul_mem h15 hB
  have h17 : rootZStep17 ∈ K := rootZStep17_eq ▸ K.mul_mem h16 hB
  have h18 : rootZStep18 ∈ K := rootZStep18_eq ▸ K.mul_mem h17 hB
  have h19 : rootZStep19 ∈ K := rootZStep19_eq ▸ K.mul_mem h18 hA
  have h20 : rootZStep20 ∈ K := rootZStep20_eq ▸ K.mul_mem h19 hA
  have he : rootZStep20 = transvection (show (0 : Fin 3) ≠ 1 by decide) z := by
    apply Subtype.ext
    decide +kernel
  exact he ▸ h20

end Held.InvolutionFixedData.TwoA.ProjectiveComparison
