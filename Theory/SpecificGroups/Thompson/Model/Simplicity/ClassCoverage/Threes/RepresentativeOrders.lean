module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordProducts0
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordProducts1
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordProducts2
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordProducts3
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordProducts4
public import Theory.SpecificGroups.Thompson.Model.Simplicity.ClassCoverage.Threes.WordProducts5

/-!
# Certified orders of the three Thompson order-three representatives

Packed binary products establish cube identities for the two non-generator
words. Entries `(0,4)` and `(0,5)` distinguish them from the identity. Together
with the certified order of `b`, primality of three gives all three exact orders.
Source: the ATLAS Thompson class words, recorded in `Threes/source/README.md`.
-/

namespace Thompson.Simplicity
open ThreeWordCertificate
set_option maxRecDepth 10000

private def b2Value : Model := generatorB * generatorB

private theorem b2_value : matrixHom b2Value = BinaryMatrix.decode 248 b2Rows := by
  rw [b2Value, map_mul, matrixHom_generatorB]
  exact b2_product

private def abValue : Model := generatorA * generatorB

private theorem ab_value : matrixHom abValue = BinaryMatrix.decode 248 abRows := by
  rw [abValue, map_mul, matrixHom_generatorA, matrixHom_generatorB]
  exact ab_product

private def ab2Value : Model := generatorA * b2Value

private theorem ab2_value : matrixHom ab2Value = BinaryMatrix.decode 248 ab2Rows := by
  rw [ab2Value, map_mul, matrixHom_generatorA, b2_value]
  exact ab2_product

private def ababValue : Model := abValue * abValue

private theorem abab_value : matrixHom ababValue = BinaryMatrix.decode 248 ababRows := by
  rw [ababValue, map_mul, ab_value]
  exact abab_product

private def uValue : Model := ababValue * ab2Value

private theorem u_value : matrixHom uValue = BinaryMatrix.decode 248 uRows := by
  rw [uValue, map_mul, abab_value, ab2_value]
  exact u_product

private def u2Value : Model := uValue * uValue

private theorem u2_value : matrixHom u2Value = BinaryMatrix.decode 248 u2Rows := by
  rw [u2Value, map_mul, u_value]
  exact u2_product

private def u3Value : Model := u2Value * uValue

private theorem u3_value : matrixHom u3Value = BinaryMatrix.decode 248 u3Rows := by
  rw [u3Value, map_mul, u2_value, u_value]
  exact u3_product

private def rBValue : Model := u3Value * u3Value

private theorem rB_value : matrixHom rBValue = BinaryMatrix.decode 248 rBRows := by
  rw [rBValue, map_mul, u3_value]
  exact rB_product

private def rB2Value : Model := rBValue * rBValue

private theorem rB2_value : matrixHom rB2Value = BinaryMatrix.decode 248 rB2Rows := by
  rw [rB2Value, map_mul, rB_value]
  exact rB2_product

private def rB3Value : Model := rB2Value * rBValue

private theorem rB3_value : matrixHom rB3Value = 1 := by
  rw [rB3Value, map_mul, rB2_value, rB_value]
  exact rB3_product

private def b2aValue : Model := b2Value * generatorA

private theorem b2a_value : matrixHom b2aValue = BinaryMatrix.decode 248 b2aRows := by
  rw [b2aValue, map_mul, b2_value, matrixHom_generatorA]
  exact b2a_product

private def vInv0Value : Model := b2aValue * b2aValue

private theorem vInv0_value : matrixHom vInv0Value = BinaryMatrix.decode 248 vInv0Rows := by
  rw [vInv0Value, map_mul, b2a_value]
  exact vInv0_product

private def vInvValue : Model := vInv0Value * b2Value

private theorem vInv_value : matrixHom vInvValue = BinaryMatrix.decode 248 vInvRows := by
  rw [vInvValue, map_mul, vInv0_value, b2_value]
  exact vInv_product

private def v0Value : Model := generatorB * generatorA

private theorem v0_value : matrixHom v0Value = BinaryMatrix.decode 248 v0Rows := by
  rw [v0Value, map_mul, matrixHom_generatorB, matrixHom_generatorA]
  exact v0_product

private def v1Value : Model := v0Value * v0Value

private theorem v1_value : matrixHom v1Value = BinaryMatrix.decode 248 v1Rows := by
  rw [v1Value, map_mul, v0_value]
  exact v1_product

private def vValue : Model := v1Value * generatorB

private theorem v_value : matrixHom vValue = BinaryMatrix.decode 248 vRows := by
  rw [vValue, map_mul, v1_value, matrixHom_generatorB]
  exact v_product

private def c0Value : Model := generatorA * vInvValue

private theorem c0_value : matrixHom c0Value = BinaryMatrix.decode 248 c0Rows := by
  rw [c0Value, map_mul, matrixHom_generatorA, vInv_value]
  exact c0_product

private def c1Value : Model := c0Value * generatorA

private theorem c1_value : matrixHom c1Value = BinaryMatrix.decode 248 c1Rows := by
  rw [c1Value, map_mul, c0_value, matrixHom_generatorA]
  exact c1_product

private def cValue : Model := c1Value * vValue

private theorem c_value : matrixHom cValue = BinaryMatrix.decode 248 cRows := by
  rw [cValue, map_mul, c1_value, v_value]
  exact c_product

private def rCValue : Model := cValue * cValue

private theorem rC_value : matrixHom rCValue = BinaryMatrix.decode 248 rCRows := by
  rw [rCValue, map_mul, c_value]
  exact rC_product

private def rC2Value : Model := rCValue * rCValue

private theorem rC2_value : matrixHom rC2Value = BinaryMatrix.decode 248 rC2Rows := by
  rw [rC2Value, map_mul, rC_value]
  exact rC2_product

private def rC3Value : Model := rC2Value * rCValue

private theorem rC3_value : matrixHom rC3Value = 1 := by
  rw [rC3Value, map_mul, rC2_value, rC_value]
  exact rC3_product

private theorem representative_two_value : primeRepresentative 2 = rBValue := by
  simp [primeRepresentative, rBValue, u3Value, u2Value, uValue, ababValue,
    abValue, ab2Value, b2Value, pow_succ, mul_assoc]

private theorem representative_three_value : primeRepresentative 3 = rCValue := by
  have ha : generatorA⁻¹ = generatorA :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using generatorA_sq)
  have hb : generatorB⁻¹ = generatorB ^ 2 :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_succ'] using generatorB_cube)
  simp [primeRepresentative, commutatorWord, rCValue, cValue, c1Value, c0Value,
    vValue, v1Value, v0Value, vInvValue, vInv0Value, b2aValue, b2Value,
    mul_inv_rev, ha, hb, pow_succ, mul_assoc]

/-- The second non-generator candidate has exact order three. -/
public theorem orderOf_primeRepresentative_two : orderOf (primeRepresentative 2) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [representative_two_value]
  apply orderOf_eq_prime
  · apply matrixHom_injective
    simpa only [rB3Value, rB2Value, pow_succ, pow_zero, one_mul, map_one] using rB3_value
  · intro h
    have he := congrArg (fun m : AtlasMatrix => m 0 4) (rB_value.symm.trans (congrArg matrixHom h))
    have hn : (BinaryMatrix.decode 248 rBRows) 0 4 ≠ (1 : AtlasMatrix) 0 4 := by
      decide +kernel
    exact hn he

/-- The commutator-square candidate has exact order three. -/
public theorem orderOf_primeRepresentative_three : orderOf (primeRepresentative 3) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [representative_three_value]
  apply orderOf_eq_prime
  · apply matrixHom_injective
    simpa only [rC3Value, rC2Value, pow_succ, pow_zero, one_mul, map_one] using rC3_value
  · intro h
    have he := congrArg (fun m : AtlasMatrix => m 0 5) (rC_value.symm.trans (congrArg matrixHom h))
    have hn : (BinaryMatrix.decode 248 rCRows) 0 5 ≠ (1 : AtlasMatrix) 0 5 := by
      decide +kernel
    exact hn he

end Thompson.Simplicity
