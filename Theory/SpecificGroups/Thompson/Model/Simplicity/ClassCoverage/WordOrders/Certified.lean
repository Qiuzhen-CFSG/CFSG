module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products00
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products01
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products02
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products03
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products04
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products05
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products06
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products07
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products08
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products09
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products10
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products11
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products12
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products13
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.WordOrders.Products14

/-!
# Packed certificates for Thompson prime representative orders

Literal packed rows witness products in the fixed 248-dimensional binary
representation. `BinaryMatrix.decode_mul_list` turns kernel-checked row products
into matrix identities. The Python generator supplies no proof oracle.

Source: https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ , class words
(R. A. Wilson, S. J. Nickerson and J. N. Bray). Matrix provenance is in
`Model/source/README.md`; reproduction is in `WordOrders/source/Generate.py`.
-/

namespace Thompson.Simplicity
open PrimeWordCertificate
set_option maxRecDepth 10000

private def w2Value : Model := generatorA * generatorB

private theorem w2_value : matrixHom w2Value = BinaryMatrix.decode 248 w2Rows := by
  rw [w2Value, map_mul, matrixHom_generatorA, matrixHom_generatorB]
  exact w2_product

private def w3Value : Model := generatorB * w2Value

private theorem w3_value : matrixHom w3Value = BinaryMatrix.decode 248 w3Rows := by
  rw [w3Value, map_mul, matrixHom_generatorB, w2_value]
  exact w3_product

private def w4Value : Model := w2Value * w3Value

private theorem w4_value : matrixHom w4Value = BinaryMatrix.decode 248 w4Rows := by
  rw [w4Value, map_mul, w2_value, w3_value]
  exact w4_product

private def w5Value : Model := w4Value * w4Value

private theorem w5_value : matrixHom w5Value = BinaryMatrix.decode 248 w5Rows := by
  rw [w5Value, map_mul, w4_value]
  exact w5_product

private def w6Value : Model := generatorB * generatorA

private theorem w6_value : matrixHom w6Value = BinaryMatrix.decode 248 w6Rows := by
  rw [w6Value, map_mul, matrixHom_generatorB, matrixHom_generatorA]
  exact w6_product

private def w7Value : Model := generatorA * w6Value

private theorem w7_value : matrixHom w7Value = BinaryMatrix.decode 248 w7Rows := by
  rw [w7Value, map_mul, matrixHom_generatorA, w6_value]
  exact w7_product

private def w8Value : Model := w6Value * w6Value

private theorem w8_value : matrixHom w8Value = BinaryMatrix.decode 248 w8Rows := by
  rw [w8Value, map_mul, w6_value]
  exact w8_product

private def w9Value : Model := w7Value * w8Value

private theorem w9_value : matrixHom w9Value = BinaryMatrix.decode 248 w9Rows := by
  rw [w9Value, map_mul, w7_value, w8_value]
  exact w9_product

private def w10Value : Model := generatorB * generatorB

private theorem w10_value : matrixHom w10Value = BinaryMatrix.decode 248 w10Rows := by
  rw [w10Value, map_mul, matrixHom_generatorB]
  exact w10_product

private def w11Value : Model := w6Value * w10Value

private theorem w11_value : matrixHom w11Value = BinaryMatrix.decode 248 w11Rows := by
  rw [w11Value, map_mul, w6_value, w10_value]
  exact w11_product

private def w12Value : Model := w8Value * w11Value

private theorem w12_value : matrixHom w12Value = BinaryMatrix.decode 248 w12Rows := by
  rw [w12Value, map_mul, w8_value, w11_value]
  exact w12_product

private def w13Value : Model := w9Value * w12Value

private theorem w13_value : matrixHom w13Value = BinaryMatrix.decode 248 w13Rows := by
  rw [w13Value, map_mul, w9_value, w12_value]
  exact w13_product

private def w14Value : Model := generatorA * w10Value

private theorem w14_value : matrixHom w14Value = BinaryMatrix.decode 248 w14Rows := by
  rw [w14Value, map_mul, matrixHom_generatorA, w10_value]
  exact w14_product

private def w15Value : Model := w2Value * w6Value

private theorem w15_value : matrixHom w15Value = BinaryMatrix.decode 248 w15Rows := by
  rw [w15Value, map_mul, w2_value, w6_value]
  exact w15_product

private def w16Value : Model := w14Value * w15Value

private theorem w16_value : matrixHom w16Value = BinaryMatrix.decode 248 w16Rows := by
  rw [w16Value, map_mul, w14_value, w15_value]
  exact w16_product

private def w17Value : Model := w10Value * w2Value

private theorem w17_value : matrixHom w17Value = BinaryMatrix.decode 248 w17Rows := by
  rw [w17Value, map_mul, w10_value, w2_value]
  exact w17_product

private def w18Value : Model := w17Value * w11Value

private theorem w18_value : matrixHom w18Value = BinaryMatrix.decode 248 w18Rows := by
  rw [w18Value, map_mul, w17_value, w11_value]
  exact w18_product

private def w19Value : Model := w16Value * w18Value

private theorem w19_value : matrixHom w19Value = BinaryMatrix.decode 248 w19Rows := by
  rw [w19Value, map_mul, w16_value, w18_value]
  exact w19_product

private def w20Value : Model := w13Value * w19Value

private theorem w20_value : matrixHom w20Value = BinaryMatrix.decode 248 w20Rows := by
  rw [w20Value, map_mul, w13_value, w19_value]
  exact w20_product

private def w21Value : Model := w7Value * w3Value

private theorem w21_value : matrixHom w21Value = BinaryMatrix.decode 248 w21Rows := by
  rw [w21Value, map_mul, w7_value, w3_value]
  exact w21_product

private def w22Value : Model := w21Value * w9Value

private theorem w22_value : matrixHom w22Value = BinaryMatrix.decode 248 w22Rows := by
  rw [w22Value, map_mul, w21_value, w9_value]
  exact w22_product

private def w23Value : Model := w2Value * w2Value

private theorem w23_value : matrixHom w23Value = BinaryMatrix.decode 248 w23Rows := by
  rw [w23Value, map_mul, w2_value]
  exact w23_product

private def w24Value : Model := w3Value * w23Value

private theorem w24_value : matrixHom w24Value = BinaryMatrix.decode 248 w24Rows := by
  rw [w24Value, map_mul, w3_value, w23_value]
  exact w24_product

private def w25Value : Model := w3Value * w11Value

private theorem w25_value : matrixHom w25Value = BinaryMatrix.decode 248 w25Rows := by
  rw [w25Value, map_mul, w3_value, w11_value]
  exact w25_product

private def w26Value : Model := w24Value * w25Value

private theorem w26_value : matrixHom w26Value = BinaryMatrix.decode 248 w26Rows := by
  rw [w26Value, map_mul, w24_value, w25_value]
  exact w26_product

private def w27Value : Model := w22Value * w26Value

private theorem w27_value : matrixHom w27Value = BinaryMatrix.decode 248 w27Rows := by
  rw [w27Value, map_mul, w22_value, w26_value]
  exact w27_product

private def w28Value : Model := w2Value * w7Value

private theorem w28_value : matrixHom w28Value = BinaryMatrix.decode 248 w28Rows := by
  rw [w28Value, map_mul, w2_value, w7_value]
  exact w28_product

private def w29Value : Model := w3Value * w7Value

private theorem w29_value : matrixHom w29Value = BinaryMatrix.decode 248 w29Rows := by
  rw [w29Value, map_mul, w3_value, w7_value]
  exact w29_product

private def w30Value : Model := w28Value * w29Value

private theorem w30_value : matrixHom w30Value = BinaryMatrix.decode 248 w30Rows := by
  rw [w30Value, map_mul, w28_value, w29_value]
  exact w30_product

private def w31Value : Model := w3Value * w3Value

private theorem w31_value : matrixHom w31Value = BinaryMatrix.decode 248 w31Rows := by
  rw [w31Value, map_mul, w3_value]
  exact w31_product

private def w32Value : Model := w31Value * w29Value

private theorem w32_value : matrixHom w32Value = BinaryMatrix.decode 248 w32Rows := by
  rw [w32Value, map_mul, w31_value, w29_value]
  exact w32_product

private def w33Value : Model := w30Value * w32Value

private theorem w33_value : matrixHom w33Value = BinaryMatrix.decode 248 w33Rows := by
  rw [w33Value, map_mul, w30_value, w32_value]
  exact w33_product

private def w34Value : Model := w6Value * w3Value

private theorem w34_value : matrixHom w34Value = BinaryMatrix.decode 248 w34Rows := by
  rw [w34Value, map_mul, w6_value, w3_value]
  exact w34_product

private def w35Value : Model := w34Value * w29Value

private theorem w35_value : matrixHom w35Value = BinaryMatrix.decode 248 w35Rows := by
  rw [w35Value, map_mul, w34_value, w29_value]
  exact w35_product

private def w36Value : Model := w3Value * w14Value

private theorem w36_value : matrixHom w36Value = BinaryMatrix.decode 248 w36Rows := by
  rw [w36Value, map_mul, w3_value, w14_value]
  exact w36_product

private def w37Value : Model := w29Value * w36Value

private theorem w37_value : matrixHom w37Value = BinaryMatrix.decode 248 w37Rows := by
  rw [w37Value, map_mul, w29_value, w36_value]
  exact w37_product

private def w38Value : Model := w35Value * w37Value

private theorem w38_value : matrixHom w38Value = BinaryMatrix.decode 248 w38Rows := by
  rw [w38Value, map_mul, w35_value, w37_value]
  exact w38_product

private def w39Value : Model := w33Value * w38Value

private theorem w39_value : matrixHom w39Value = BinaryMatrix.decode 248 w39Rows := by
  rw [w39Value, map_mul, w33_value, w38_value]
  exact w39_product

private def r4p2Value : Model := w5Value * w5Value

private theorem r4p2_value : matrixHom r4p2Value = BinaryMatrix.decode 248 r4p2Rows := by
  rw [r4p2Value, map_mul, w5_value]
  exact r4p2_product

private def r4p3Value : Model := w5Value * r4p2Value

private theorem r4p3_value : matrixHom r4p3Value = BinaryMatrix.decode 248 r4p3Rows := by
  rw [r4p3Value, map_mul, w5_value, r4p2_value]
  exact r4p3_product

private def r4p5Value : Model := r4p2Value * r4p3Value

private theorem r4p5_value : matrixHom r4p5Value = 1 := by
  rw [r4p5Value, map_mul, r4p2_value, r4p3_value]
  exact r4p5_product

private def r5p2Value : Model := w20Value * w20Value

private theorem r5p2_value : matrixHom r5p2Value = BinaryMatrix.decode 248 r5p2Rows := by
  rw [r5p2Value, map_mul, w20_value]
  exact r5p2_product

private def r5p3Value : Model := w20Value * r5p2Value

private theorem r5p3_value : matrixHom r5p3Value = BinaryMatrix.decode 248 r5p3Rows := by
  rw [r5p3Value, map_mul, w20_value, r5p2_value]
  exact r5p3_product

private def r5p4Value : Model := r5p2Value * r5p2Value

private theorem r5p4_value : matrixHom r5p4Value = BinaryMatrix.decode 248 r5p4Rows := by
  rw [r5p4Value, map_mul, r5p2_value]
  exact r5p4_product

private def r5p7Value : Model := r5p3Value * r5p4Value

private theorem r5p7_value : matrixHom r5p7Value = 1 := by
  rw [r5p7Value, map_mul, r5p3_value, r5p4_value]
  exact r5p7_product

private def r6p2Value : Model := w27Value * w27Value

private theorem r6p2_value : matrixHom r6p2Value = BinaryMatrix.decode 248 r6p2Rows := by
  rw [r6p2Value, map_mul, w27_value]
  exact r6p2_product

private def r6p3Value : Model := w27Value * r6p2Value

private theorem r6p3_value : matrixHom r6p3Value = BinaryMatrix.decode 248 r6p3Rows := by
  rw [r6p3Value, map_mul, w27_value, r6p2_value]
  exact r6p3_product

private def r6p6Value : Model := r6p3Value * r6p3Value

private theorem r6p6_value : matrixHom r6p6Value = BinaryMatrix.decode 248 r6p6Rows := by
  rw [r6p6Value, map_mul, r6p3_value]
  exact r6p6_product

private def r6p4Value : Model := r6p2Value * r6p2Value

private theorem r6p4_value : matrixHom r6p4Value = BinaryMatrix.decode 248 r6p4Rows := by
  rw [r6p4Value, map_mul, r6p2_value]
  exact r6p4_product

private def r6p7Value : Model := r6p3Value * r6p4Value

private theorem r6p7_value : matrixHom r6p7Value = BinaryMatrix.decode 248 r6p7Rows := by
  rw [r6p7Value, map_mul, r6p3_value, r6p4_value]
  exact r6p7_product

private def r6p13Value : Model := r6p6Value * r6p7Value

private theorem r6p13_value : matrixHom r6p13Value = 1 := by
  rw [r6p13Value, map_mul, r6p6_value, r6p7_value]
  exact r6p13_product

private def r8p2Value : Model := w39Value * w39Value

private theorem r8p2_value : matrixHom r8p2Value = BinaryMatrix.decode 248 r8p2Rows := by
  rw [r8p2Value, map_mul, w39_value]
  exact r8p2_product

private def r8p3Value : Model := w39Value * r8p2Value

private theorem r8p3_value : matrixHom r8p3Value = BinaryMatrix.decode 248 r8p3Rows := by
  rw [r8p3Value, map_mul, w39_value, r8p2_value]
  exact r8p3_product

private def r8p4Value : Model := r8p2Value * r8p2Value

private theorem r8p4_value : matrixHom r8p4Value = BinaryMatrix.decode 248 r8p4Rows := by
  rw [r8p4Value, map_mul, r8p2_value]
  exact r8p4_product

private def r8p7Value : Model := r8p3Value * r8p4Value

private theorem r8p7_value : matrixHom r8p7Value = BinaryMatrix.decode 248 r8p7Rows := by
  rw [r8p7Value, map_mul, r8p3_value, r8p4_value]
  exact r8p7_product

private def r8p8Value : Model := r8p4Value * r8p4Value

private theorem r8p8_value : matrixHom r8p8Value = BinaryMatrix.decode 248 r8p8Rows := by
  rw [r8p8Value, map_mul, r8p4_value]
  exact r8p8_product

private def r8p15Value : Model := r8p7Value * r8p8Value

private theorem r8p15_value : matrixHom r8p15Value = BinaryMatrix.decode 248 r8p15Rows := by
  rw [r8p15Value, map_mul, r8p7_value, r8p8_value]
  exact r8p15_product

private def r8p16Value : Model := r8p8Value * r8p8Value

private theorem r8p16_value : matrixHom r8p16Value = BinaryMatrix.decode 248 r8p16Rows := by
  rw [r8p16Value, map_mul, r8p8_value]
  exact r8p16_product

private def r8p31Value : Model := r8p15Value * r8p16Value

private theorem r8p31_value : matrixHom r8p31Value = 1 := by
  rw [r8p31Value, map_mul, r8p15_value, r8p16_value]
  exact r8p31_product

private theorem representative_4_value : primeRepresentative 4 = w5Value := by
  have ha : generatorA⁻¹ = generatorA :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generatorA_sq)
  have hb : generatorB⁻¹ = generatorB ^ 2 :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_succ'] using generatorB_cube)
  simp [primeRepresentative, commutatorWord, ha, hb, w5Value, w4Value, w3Value, w2Value, pow_succ, mul_assoc]

private theorem r4_power2 : w5Value ^ 2 = r4p2Value := by
  calc
    _ = w5Value ^ 1 * w5Value ^ 1 := pow_add _ 1 1
    _ = _ := by simp only [pow_one]; rfl

private theorem r4_power3 : w5Value ^ 3 = r4p3Value := by
  calc
    _ = w5Value ^ 1 * w5Value ^ 2 := pow_add _ 1 2
    _ = _ := by simp only [pow_one, r4_power2]; rfl

private theorem r4_power5 : w5Value ^ 5 = r4p5Value := by
  calc
    _ = w5Value ^ 2 * w5Value ^ 3 := pow_add _ 2 3
    _ = _ := by simp only [r4_power2, r4_power3]; rfl

/-- The fixed representative at index 4 has exact order 5. -/
public theorem orderOf_primeRepresentative_four : orderOf (primeRepresentative 4) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [representative_4_value]
  apply orderOf_eq_prime
  · apply matrixHom_injective
    rw [r4_power5, map_one]
    exact r4p5_value
  · intro h
    have he := congrArg (fun m : AtlasMatrix => m 0 0)
      (w5_value.symm.trans (congrArg matrixHom h))
    have hn : (BinaryMatrix.decode 248 w5Rows) 0 0 ≠ (1 : AtlasMatrix) 0 0 := by
      decide +kernel
    exact hn he

private theorem representative_5_value : primeRepresentative 5 = w20Value := by
  simp [primeRepresentative, w20Value, w19Value, w18Value, w17Value, w16Value, w15Value, w14Value, w13Value, w12Value, w11Value, w10Value, w9Value, w8Value, w7Value, w6Value, w2Value, pow_succ, mul_assoc]

private theorem r5_power2 : w20Value ^ 2 = r5p2Value := by
  calc
    _ = w20Value ^ 1 * w20Value ^ 1 := pow_add _ 1 1
    _ = _ := by simp only [pow_one]; rfl

private theorem r5_power3 : w20Value ^ 3 = r5p3Value := by
  calc
    _ = w20Value ^ 1 * w20Value ^ 2 := pow_add _ 1 2
    _ = _ := by simp only [pow_one, r5_power2]; rfl

private theorem r5_power4 : w20Value ^ 4 = r5p4Value := by
  calc
    _ = w20Value ^ 2 * w20Value ^ 2 := pow_add _ 2 2
    _ = _ := by simp only [r5_power2]; rfl

private theorem r5_power7 : w20Value ^ 7 = r5p7Value := by
  calc
    _ = w20Value ^ 3 * w20Value ^ 4 := pow_add _ 3 4
    _ = _ := by simp only [r5_power3, r5_power4]; rfl

/-- The fixed representative at index 5 has exact order 7. -/
public theorem orderOf_primeRepresentative_five : orderOf (primeRepresentative 5) = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  rw [representative_5_value]
  apply orderOf_eq_prime
  · apply matrixHom_injective
    rw [r5_power7, map_one]
    exact r5p7_value
  · intro h
    have he := congrArg (fun m : AtlasMatrix => m 0 0)
      (w20_value.symm.trans (congrArg matrixHom h))
    have hn : (BinaryMatrix.decode 248 w20Rows) 0 0 ≠ (1 : AtlasMatrix) 0 0 := by
      decide +kernel
    exact hn he

private theorem representative_6_value : primeRepresentative 6 = w27Value := by
  simp [primeRepresentative, w27Value, w26Value, w25Value, w24Value, w23Value, w22Value, w21Value, w11Value, w10Value, w9Value, w8Value, w7Value, w6Value, w3Value, w2Value, pow_succ, mul_assoc]

private theorem r6_power2 : w27Value ^ 2 = r6p2Value := by
  calc
    _ = w27Value ^ 1 * w27Value ^ 1 := pow_add _ 1 1
    _ = _ := by simp only [pow_one]; rfl

private theorem r6_power3 : w27Value ^ 3 = r6p3Value := by
  calc
    _ = w27Value ^ 1 * w27Value ^ 2 := pow_add _ 1 2
    _ = _ := by simp only [pow_one, r6_power2]; rfl

private theorem r6_power6 : w27Value ^ 6 = r6p6Value := by
  calc
    _ = w27Value ^ 3 * w27Value ^ 3 := pow_add _ 3 3
    _ = _ := by simp only [r6_power3]; rfl

private theorem r6_power4 : w27Value ^ 4 = r6p4Value := by
  calc
    _ = w27Value ^ 2 * w27Value ^ 2 := pow_add _ 2 2
    _ = _ := by simp only [r6_power2]; rfl

private theorem r6_power7 : w27Value ^ 7 = r6p7Value := by
  calc
    _ = w27Value ^ 3 * w27Value ^ 4 := pow_add _ 3 4
    _ = _ := by simp only [r6_power3, r6_power4]; rfl

private theorem r6_power13 : w27Value ^ 13 = r6p13Value := by
  calc
    _ = w27Value ^ 6 * w27Value ^ 7 := pow_add _ 6 7
    _ = _ := by simp only [r6_power6, r6_power7]; rfl

/-- The fixed representative at index 6 has exact order 13. -/
public theorem orderOf_primeRepresentative_six : orderOf (primeRepresentative 6) = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  rw [representative_6_value]
  apply orderOf_eq_prime
  · apply matrixHom_injective
    rw [r6_power13, map_one]
    exact r6p13_value
  · intro h
    have he := congrArg (fun m : AtlasMatrix => m 0 1)
      (w27_value.symm.trans (congrArg matrixHom h))
    have hn : (BinaryMatrix.decode 248 w27Rows) 0 1 ≠ (1 : AtlasMatrix) 0 1 := by
      decide +kernel
    exact hn he

private theorem representative_8_value : primeRepresentative 8 = w39Value := by
  simp [primeRepresentative, word, w39Value, w38Value, w37Value, w36Value, w35Value, w34Value, w33Value, w32Value, w31Value, w30Value, w29Value, w28Value, w14Value, w10Value, w7Value, w6Value, w3Value, w2Value, mul_assoc]

private theorem r8_power2 : w39Value ^ 2 = r8p2Value := by
  calc
    _ = w39Value ^ 1 * w39Value ^ 1 := pow_add _ 1 1
    _ = _ := by simp only [pow_one]; rfl

private theorem r8_power3 : w39Value ^ 3 = r8p3Value := by
  calc
    _ = w39Value ^ 1 * w39Value ^ 2 := pow_add _ 1 2
    _ = _ := by simp only [pow_one, r8_power2]; rfl

private theorem r8_power4 : w39Value ^ 4 = r8p4Value := by
  calc
    _ = w39Value ^ 2 * w39Value ^ 2 := pow_add _ 2 2
    _ = _ := by simp only [r8_power2]; rfl

private theorem r8_power7 : w39Value ^ 7 = r8p7Value := by
  calc
    _ = w39Value ^ 3 * w39Value ^ 4 := pow_add _ 3 4
    _ = _ := by simp only [r8_power3, r8_power4]; rfl

private theorem r8_power8 : w39Value ^ 8 = r8p8Value := by
  calc
    _ = w39Value ^ 4 * w39Value ^ 4 := pow_add _ 4 4
    _ = _ := by simp only [r8_power4]; rfl

private theorem r8_power15 : w39Value ^ 15 = r8p15Value := by
  calc
    _ = w39Value ^ 7 * w39Value ^ 8 := pow_add _ 7 8
    _ = _ := by simp only [r8_power7, r8_power8]; rfl

private theorem r8_power16 : w39Value ^ 16 = r8p16Value := by
  calc
    _ = w39Value ^ 8 * w39Value ^ 8 := pow_add _ 8 8
    _ = _ := by simp only [r8_power8]; rfl

private theorem r8_power31 : w39Value ^ 31 = r8p31Value := by
  calc
    _ = w39Value ^ 15 * w39Value ^ 16 := pow_add _ 15 16
    _ = _ := by simp only [r8_power15, r8_power16]; rfl

/-- The fixed representative at index 8 has exact order 31. -/
public theorem orderOf_primeRepresentative_eight : orderOf (primeRepresentative 8) = 31 := by
  let : Fact (Nat.Prime 31) := ⟨by decide⟩
  rw [representative_8_value]
  apply orderOf_eq_prime
  · apply matrixHom_injective
    rw [r8_power31, map_one]
    exact r8p31_value
  · intro h
    have he := congrArg (fun m : AtlasMatrix => m 0 2)
      (w39_value.symm.trans (congrArg matrixHom h))
    have hn : (BinaryMatrix.decode 248 w39Rows) 0 2 ≠ (1 : AtlasMatrix) 0 2 := by
      decide +kernel
    exact hn he

end Thompson.Simplicity
