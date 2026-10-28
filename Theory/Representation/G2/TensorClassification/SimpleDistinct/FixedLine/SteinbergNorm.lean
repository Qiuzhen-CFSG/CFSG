module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine.SteinbergReduction
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine.SteinbergNorm.Coefficient

/-!+# Nonzero norm in the full G₂ Steinberg Frobenius word

The highest coefficient of the literal six-root norm is one. The natural tensor
cube computes each factor coefficient, Frobenius makes their product the
`(2^n - 1)`st power, and the symbolic finite-field sum evaluates to one.
Consequently the norm is nonzero, as required by `steinbergWord_fixed_of_norm`.
No simplicity, cyclicity or fixed-line uniqueness is assumed.

Source: GLS3, 2.8.6–9 and Example 2.8.10(g), used in Aschbacher–Smith G.9.3(10),
`refs/quasithin.pdf`, printed pp.354, 356–357.
-/

public noncomputable section

namespace Atlas.G2.TensorClassification.FixedLine

variable (F : Type*) [Field F] [CharP F 2] [Finite F] [Fintype F]

/-- The published full Steinberg norm has normalized highest coefficient one. -/
theorem wordHighestCoefficient_steinbergNorm {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    wordHighestCoefficient F (List.replicate n .steinberg) (steinbergNorm F n) = 1 := by
  rw [steinbergNorm, map_sum]
  simp_rw [SteinbergNormCalculation.word_coefficient,
    SteinbergNormCalculation.factor_coefficient, pow_zero, one_mul]
  rw [← hF, Nat.card_eq_fintype_card]
  exact SteinbergNormCalculation.polynomial_sum F

/-- The literal norm over all six field-valued root parameters is nonzero. -/
theorem steinbergNorm_ne_zero {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    steinbergNorm F n ≠ 0 := by
  intro h
  have hc := wordHighestCoefficient_steinbergNorm F hF
  rw [h, map_zero] at hc
  exact zero_ne_one hc

end Atlas.G2.TensorClassification.FixedLine

end
