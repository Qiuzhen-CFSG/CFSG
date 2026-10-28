module

public import Theory.SpecificGroups.Thompson.Model.Simplicity.PrimeRepresentatives
public import Theory.SpecificGroups.Thompson.Model.Simplicity.Reduction
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationLow.ThreeB.Products0
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationLow.ThreeB.Products1
public import Theory.SpecificGroups.Thompson.Model.Simplicity.NormalGenerationLow.ThreeB.Products2

/-!
# Normal generation by the Thompson three-word at index two

Set `r = (ababab²)^6` and `g = ab²`. The packed matrix certificates prove
`(g⁻¹*r*g*a)^27 = 1`, written with `g⁻¹ = ba` to avoid matrix inversion.
In the quotient killing `r`, this gives `a^27 = 1`. Together with `a² = 1`
it kills `a`; the relation `(ab)^19 = 1` then kills `b` as well.

Source: the ATLAS Thompson word table,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Th/ . The additional power
relation is proved directly for the supplied matrices. Matrix provenance is
recorded in `Model/source/README.md`, and the reproducible kernel certificate
is documented in `ThreeB/source/README.md`. No class identification is used.
-/

namespace Thompson.Simplicity
open ThreeWordCertificate ThreeBNormalCertificate
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

private def baValue : Model := generatorB * generatorA

private theorem ba_value : matrixHom baValue = BinaryMatrix.decode 248 baRows := by
  rw [baValue, map_mul, matrixHom_generatorB, matrixHom_generatorA]
  exact ba_product

private def barValue : Model := baValue * rBValue

private theorem bar_value : matrixHom barValue = BinaryMatrix.decode 248 barRows := by
  rw [barValue, map_mul, ba_value, rB_value]
  exact bar_product

private def bargValue : Model := barValue * ab2Value

private theorem barg_value : matrixHom bargValue = BinaryMatrix.decode 248 bargRows := by
  rw [bargValue, map_mul, bar_value, ab2_value]
  exact barg_product

private def tValue : Model := bargValue * generatorA

private theorem t_value : matrixHom tValue = BinaryMatrix.decode 248 tRows := by
  rw [tValue, map_mul, barg_value, matrixHom_generatorA]
  exact t_product

private def t2Value : Model := tValue * tValue

private theorem t2_value : matrixHom t2Value = BinaryMatrix.decode 248 t2Rows := by
  rw [t2Value, map_mul, t_value]
  exact t2_product

private def t3Value : Model := t2Value * tValue

private theorem t3_value : matrixHom t3Value = BinaryMatrix.decode 248 t3Rows := by
  rw [t3Value, map_mul, t2_value, t_value]
  exact t3_product

private def t6Value : Model := t3Value * t3Value

private theorem t6_value : matrixHom t6Value = BinaryMatrix.decode 248 t6Rows := by
  rw [t6Value, map_mul, t3_value]
  exact t6_product

private def t12Value : Model := t6Value * t6Value

private theorem t12_value : matrixHom t12Value = BinaryMatrix.decode 248 t12Rows := by
  rw [t12Value, map_mul, t6_value]
  exact t12_product

private def t24Value : Model := t12Value * t12Value

private theorem t24_value : matrixHom t24Value = BinaryMatrix.decode 248 t24Rows := by
  rw [t24Value, map_mul, t12_value]
  exact t24_product

private def t27Value : Model := t24Value * t3Value

private theorem t27_value : matrixHom t27Value = 1 := by
  rw [t27Value, map_mul, t24_value, t3_value]
  exact t27_product

private theorem representative_two_value : primeRepresentative 2 = rBValue := by
  simp [primeRepresentative, rBValue, u3Value, u2Value, uValue, ababValue,
    abValue, ab2Value, b2Value, pow_succ, mul_assoc]

/-- A concrete odd-power relation that detects the killed representative. -/
public theorem threeB_conjugate_mul_generatorA_pow :
    (generatorB * generatorA * primeRepresentative 2 *
      (generatorA * generatorB ^ 2) * generatorA) ^ 27 = 1 := by
  have h : tValue ^ 27 = 1 := by
    apply matrixHom_injective
    simpa only [t27Value, t24Value, t12Value, t6Value, t3Value, t2Value,
      pow_succ, pow_zero, one_mul, mul_assoc, map_one] using t27_value
  simpa only [tValue, bargValue, barValue, baValue, ab2Value, b2Value,
    pow_two, representative_two_value] using h

/-- The second non-generator three-word normally generates the fixed model. -/
public theorem normalClosure_primeRepresentative_two_of_ab19
    (hab19 : (generatorA * generatorB) ^ 19 = 1) :
    Subgroup.normalClosure ({primeRepresentative 2} : Set Model) = ⊤ := by
  let N := Subgroup.normalClosure ({primeRepresentative 2} : Set Model)
  let q := QuotientGroup.mk' N
  have hrN : primeRepresentative 2 ∈ N :=
    Subgroup.subset_normalClosure (Set.mem_singleton _)
  have hqr : q (primeRepresentative 2) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hrN
  have ha2 : (q generatorA) ^ 2 = 1 := by simpa using congrArg q generatorA_sq
  have hb3 : (q generatorB) ^ 3 = 1 := by simpa using congrArg q generatorB_cube
  have ha27 : (q generatorA) ^ 27 = 1 := by
    have ht := congrArg q threeB_conjugate_mul_generatorA_pow
    have haa : q generatorA * q generatorA = 1 := by simpa only [pow_two] using ha2
    have hbb : q generatorB * (q generatorB) ^ 2 = 1 := by
      simpa only [pow_succ'] using hb3
    simp only [map_pow, map_mul, map_one, hqr, mul_one] at ht
    rw [mul_assoc (q generatorB) (q generatorA),
      ← mul_assoc (q generatorA) (q generatorA), haa, one_mul, hbb, one_mul] at ht
    exact ht
  have haN : generatorA ∈ N := (QuotientGroup.eq_one_iff _).mp
    ((pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 2 27)).mp ⟨ha2, ha27⟩)
  have hle : Subgroup.normalClosure ({generatorA} : Set Model) ≤ N :=
    Subgroup.normalClosure_le_normal (by simpa using haN)
  rw [normalClosure_generatorA_of_ab19 hab19] at hle
  exact top_unique hle

end Thompson.Simplicity
