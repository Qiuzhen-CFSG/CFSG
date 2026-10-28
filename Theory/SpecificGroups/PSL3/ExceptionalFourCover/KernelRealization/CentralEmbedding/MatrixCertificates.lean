module

public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.KernelRealization.Model

/-!
# Matrix coordinates of the three central words

The signed words from `../Source/central.json` evaluate to I, I, and zI.
Every step is checked as a product of explicit 3 by 3 matrices over F₄;
long nested matrix products are never reduced. The two order-four words
retain their source order, followed by the order-three word.
Source: Aschbacher–Smith I.1.3(6), printed p.407; GLS3 §6.1.
-/

@[expose] public section
namespace Matrix.PSL3.ExceptionalFourCover.KernelModel.CentralWords

private def inverseX : SL := ⟨!![1, z + 1, 1; 0, 0, z; z, z, z + 1], by decide +kernel⟩

private theorem inverseX_eq : matrixX⁻¹ = inverseX := by
  apply Subtype.ext
  decide +kernel

private def inverseY : SL := ⟨!![z + 1, 1, z + 1; 1, 1, z; z, 1, z + 1], by decide +kernel⟩

private theorem inverseY_eq : matrixY⁻¹ = inverseY := by
  apply Subtype.ext
  decide +kernel

def scalarZ : SL := ⟨!![z, 0, 0; 0, z, 0; 0, 0, z], by decide +kernel⟩

def fourA {G : Type*} [_root_.Group G] (a b : G) : G :=
  1 * b * a⁻¹ * b * a⁻¹ * b * b * a⁻¹ * a⁻¹ * b⁻¹ * a * b⁻¹ * b⁻¹ * b⁻¹ * b⁻¹ * a * a

theorem map_fourA {G H : Type*} [_root_.Group G] [_root_.Group H]
    (f : G →* H) (a b : G) : f (fourA a b) = fourA (f a) (f b) := by
  simp only [fourA, map_mul, map_inv, map_one]

private def fourAStep0 : SL := ⟨!![1, 0, 1; 0, z + 1, z; z + 1, 1, z], by decide +kernel⟩
private theorem fourAStep0_eq : (1 : SL) * matrixY = fourAStep0 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep1 : SL := ⟨!![z + 1, 1, z; z + 1, z + 1, 0; 0, 1, 0], by decide +kernel⟩
private theorem fourAStep1_eq : fourAStep0 * inverseX = fourAStep1 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep2 : SL := ⟨!![z, 1, z; z + 1, z, z; 0, z + 1, z], by decide +kernel⟩
private theorem fourAStep2_eq : fourAStep1 * matrixY = fourAStep2 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep3 : SL := ⟨!![1, z, 1; 0, 1, 1; z + 1, z + 1, 0], by decide +kernel⟩
private theorem fourAStep3_eq : fourAStep2 * inverseX = fourAStep3 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep4 : SL := ⟨!![z, 0, 0; z + 1, z, 0; z + 1, z, z], by decide +kernel⟩
private theorem fourAStep4_eq : fourAStep3 * matrixY = fourAStep4 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep5 : SL := ⟨!![z, 0, z; z + 1, 1, 0; z, z + 1, z + 1], by decide +kernel⟩
private theorem fourAStep5_eq : fourAStep4 * matrixY = fourAStep5 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep6 : SL := ⟨!![1, z, z + 1; z + 1, z, 1; z + 1, 0, 1], by decide +kernel⟩
private theorem fourAStep6_eq : fourAStep5 * inverseX = fourAStep6 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep7 : SL := ⟨!![0, z, 0; 1, 0, z + 1; 1, 0, 0], by decide +kernel⟩
private theorem fourAStep7_eq : fourAStep6 * inverseX = fourAStep7 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep8 : SL := ⟨!![z, z, z + 1; z, z, 1; z + 1, 1, z + 1], by decide +kernel⟩
private theorem fourAStep8_eq : fourAStep7 * inverseY = fourAStep8 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep9 : SL := ⟨!![0, 0, 1; 0, 1, 1; 1, z + 1, 1], by decide +kernel⟩
private theorem fourAStep9_eq : fourAStep8 * matrixX = fourAStep9 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep10 : SL := ⟨!![z, 1, z + 1; z + 1, 0, 1; z, z + 1, 1], by decide +kernel⟩
private theorem fourAStep10_eq : fourAStep9 * inverseY = fourAStep10 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep11 : SL := ⟨!![1, 0, 1; 0, z, 1; 0, 0, z + 1], by decide +kernel⟩
private theorem fourAStep11_eq : fourAStep10 * inverseY = fourAStep11 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep12 : SL := ⟨!![1, 0, 0; 0, z + 1, 0; 1, z + 1, z], by decide +kernel⟩
private theorem fourAStep12_eq : fourAStep11 * inverseY = fourAStep12 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep13 : SL := ⟨!![z + 1, 1, z + 1; z + 1, z + 1, 1; z + 1, 0, z + 1], by decide +kernel⟩
private theorem fourAStep13_eq : fourAStep12 * inverseY = fourAStep13 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep14 : SL := ⟨!![1, z + 1, 1; 0, 0, z; z, z, z + 1], by decide +kernel⟩
private theorem fourAStep14_eq : fourAStep13 * matrixX = fourAStep14 := by
  apply Subtype.ext
  decide +kernel

private def fourAStep15 : SL := ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩
private theorem fourAStep15_eq : fourAStep14 * matrixX = fourAStep15 := by
  apply Subtype.ext
  decide +kernel

theorem fourA_matrix : fourA matrixX matrixY = 1 := by
  rw [fourA, inverseX_eq, inverseY_eq, fourAStep0_eq, fourAStep1_eq, fourAStep2_eq, fourAStep3_eq, fourAStep4_eq, fourAStep5_eq, fourAStep6_eq, fourAStep7_eq, fourAStep8_eq, fourAStep9_eq, fourAStep10_eq, fourAStep11_eq, fourAStep12_eq, fourAStep13_eq, fourAStep14_eq, fourAStep15_eq]
  apply Subtype.ext
  decide +kernel

def fourB {G : Type*} [_root_.Group G] (a b : G) : G :=
  1 * a⁻¹ * a⁻¹ * b * a⁻¹ * a⁻¹ * b * a⁻¹ * a⁻¹ * b

theorem map_fourB {G H : Type*} [_root_.Group G] [_root_.Group H]
    (f : G →* H) (a b : G) : f (fourB a b) = fourB (f a) (f b) := by
  simp only [fourB, map_mul, map_inv, map_one]

private def fourBStep0 : SL := ⟨!![1, z + 1, 1; 0, 0, z; z, z, z + 1], by decide +kernel⟩
private theorem fourBStep0_eq : (1 : SL) * inverseX = fourBStep0 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep1 : SL := ⟨!![z + 1, 1, z + 1; z + 1, z + 1, 1; z + 1, 0, z + 1], by decide +kernel⟩
private theorem fourBStep1_eq : fourBStep0 * inverseX = fourBStep1 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep2 : SL := ⟨!![1, 0, 0; 0, z + 1, 0; 1, z + 1, z], by decide +kernel⟩
private theorem fourBStep2_eq : fourBStep1 * matrixY = fourBStep2 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep3 : SL := ⟨!![1, z + 1, 1; 0, 0, 1; z, 0, 1], by decide +kernel⟩
private theorem fourBStep3_eq : fourBStep2 * inverseX = fourBStep3 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep4 : SL := ⟨!![z + 1, 1, z + 1; z, z, z + 1; 0, z + 1, 1], by decide +kernel⟩
private theorem fourBStep4_eq : fourBStep3 * inverseX = fourBStep4 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep5 : SL := ⟨!![1, 0, 0; 0, z, 0; z + 1, z + 1, z + 1], by decide +kernel⟩
private theorem fourBStep5_eq : fourBStep4 * matrixY = fourBStep5 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep6 : SL := ⟨!![1, z + 1, 1; 0, 0, z + 1; z, z + 1, 0], by decide +kernel⟩
private theorem fourBStep6_eq : fourBStep5 * inverseX = fourBStep6 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep7 : SL := ⟨!![z + 1, 1, z + 1; 1, 1, z; z, 1, z + 1], by decide +kernel⟩
private theorem fourBStep7_eq : fourBStep6 * inverseX = fourBStep7 := by
  apply Subtype.ext
  decide +kernel

private def fourBStep8 : SL := ⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide +kernel⟩
private theorem fourBStep8_eq : fourBStep7 * matrixY = fourBStep8 := by
  apply Subtype.ext
  decide +kernel

theorem fourB_matrix : fourB matrixX matrixY = 1 := by
  rw [fourB, inverseX_eq, fourBStep0_eq, fourBStep1_eq, fourBStep2_eq, fourBStep3_eq, fourBStep4_eq, fourBStep5_eq, fourBStep6_eq, fourBStep7_eq, fourBStep8_eq]
  apply Subtype.ext
  decide +kernel

def three {G : Type*} [_root_.Group G] (a b : G) : G :=
  1 * b⁻¹ * a * b⁻¹ * b⁻¹ * a⁻¹ * b * a⁻¹ * b * a⁻¹ * b⁻¹ * a * b * b * a

theorem map_three {G H : Type*} [_root_.Group G] [_root_.Group H]
    (f : G →* H) (a b : G) : f (three a b) = three (f a) (f b) := by
  simp only [three, map_mul, map_inv, map_one]

private def threeStep0 : SL := ⟨!![z + 1, 1, z + 1; 1, 1, z; z, 1, z + 1], by decide +kernel⟩
private theorem threeStep0_eq : (1 : SL) * inverseY = threeStep0 := by
  apply Subtype.ext
  decide +kernel

private def threeStep1 : SL := ⟨!![1, z + 1, 1; 0, 0, z + 1; z, z + 1, 0], by decide +kernel⟩
private theorem threeStep1_eq : threeStep0 * matrixX = threeStep1 := by
  apply Subtype.ext
  decide +kernel

private def threeStep2 : SL := ⟨!![z, z + 1, 1; 1, z + 1, z; z, 1, 0], by decide +kernel⟩
private theorem threeStep2_eq : threeStep1 * inverseY = threeStep2 := by
  apply Subtype.ext
  decide +kernel

private def threeStep3 : SL := ⟨!![0, 0, z + 1; z + 1, 0, z + 1; 0, z + 1, z + 1], by decide +kernel⟩
private theorem threeStep3_eq : threeStep2 * inverseY = threeStep3 := by
  apply Subtype.ext
  decide +kernel

private def threeStep4 : SL := ⟨!![1, 1, z; z, z + 1, 1; 1, 1, z + 1], by decide +kernel⟩
private theorem threeStep4_eq : threeStep3 * inverseX = threeStep4 := by
  apply Subtype.ext
  decide +kernel

private def threeStep5 : SL := ⟨!![0, 1, 0; 1, z + 1, 1; z + 1, 0, z], by decide +kernel⟩
private theorem threeStep5_eq : threeStep4 * matrixY = threeStep5 := by
  apply Subtype.ext
  decide +kernel

private def threeStep6 : SL := ⟨!![0, 0, z; z + 1, 1, z + 1; 0, 1, z], by decide +kernel⟩
private theorem threeStep6_eq : threeStep5 * inverseX = threeStep6 := by
  apply Subtype.ext
  decide +kernel

private def threeStep7 : SL := ⟨!![1, z, z + 1; 1, 0, 0; 1, 1, 1], by decide +kernel⟩
private theorem threeStep7_eq : threeStep6 * matrixY = threeStep7 := by
  apply Subtype.ext
  decide +kernel

private def threeStep8 : SL := ⟨!![0, z, 0; 1, z + 1, 1; z + 1, 1, 0], by decide +kernel⟩
private theorem threeStep8_eq : threeStep7 * inverseX = threeStep8 := by
  apply Subtype.ext
  decide +kernel

private def threeStep9 : SL := ⟨!![z, z, z + 1; z, z + 1, 1; z + 1, z, 0], by decide +kernel⟩
private theorem threeStep9_eq : threeStep8 * inverseY = threeStep9 := by
  apply Subtype.ext
  decide +kernel

private def threeStep10 : SL := ⟨!![0, 0, 1; z + 1, 0, z + 1; z + 1, z, 0], by decide +kernel⟩
private theorem threeStep10_eq : threeStep9 * matrixX = threeStep10 := by
  apply Subtype.ext
  decide +kernel

private def threeStep11 : SL := ⟨!![z + 1, 1, z; 1, z + 1, z; z + 1, 1, 0], by decide +kernel⟩
private theorem threeStep11_eq : threeStep10 * matrixY = threeStep11 := by
  apply Subtype.ext
  decide +kernel

private def threeStep12 : SL := ⟨!![z, 1, z; 0, 0, z + 1; z + 1, z + 1, 1], by decide +kernel⟩
private theorem threeStep12_eq : threeStep11 * matrixY = threeStep12 := by
  apply Subtype.ext
  decide +kernel

private def threeStep13 : SL := ⟨!![z, 0, 0; 0, z, 0; 0, 0, z], by decide +kernel⟩
private theorem threeStep13_eq : threeStep12 * matrixX = threeStep13 := by
  apply Subtype.ext
  decide +kernel

theorem three_matrix : three matrixX matrixY = scalarZ := by
  rw [three, inverseX_eq, inverseY_eq, threeStep0_eq, threeStep1_eq, threeStep2_eq, threeStep3_eq, threeStep4_eq, threeStep5_eq, threeStep6_eq, threeStep7_eq, threeStep8_eq, threeStep9_eq, threeStep10_eq, threeStep11_eq, threeStep12_eq, threeStep13_eq]
  apply Subtype.ext
  decide +kernel

end Matrix.PSL3.ExceptionalFourCover.KernelModel.CentralWords
