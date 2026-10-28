module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.HighestVector
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine.SteinbergNorm.ScalarSum

/-!
# The actual coefficient of a G₂ Steinberg tensor word

The Steinberg factor is the orbit span of `e₀ ⊗ (e₀ ⊗ e₁ + e₁ ⊗ e₀)`
in the natural tensor cube. Computing its `(0,0,1)` coefficient after the
six positive root actions and the longest Weyl element gives the polynomial
of `ScalarSum`. Coefficient transport then handles each genuine Frobenius
twist; tensor induction adds the exponents to `2 ^ r * (2 ^ n - 1)`.

This calculation uses the actual octonion representation and its published
highest vector. It assumes no fixed-line uniqueness, simplicity or cyclicity.
Source: GLS3, 2.8.6–9 and Example 2.8.10(g). The underlying root formulas are
from the attributed ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section

open scoped TensorProduct BigOperators CharTwo
open Atlas.G2 Atlas.G2.Restricted Atlas.G2.Explicit
open Atlas.G2.TensorClassification
namespace Atlas.G2.TensorClassification.FixedLine.SteinbergNormCalculation
variable (F : Type*) [Field F] [CharP F 2]

/-- The highest coefficient of the opposite-highest translate is the explicit
natural coefficient times the adjacent minor. -/
theorem factor_coefficient (t : Fin 6 → F) :
    factorHighestCoefficient F .steinberg
      (action F .steinberg (unipotentProduct t * Steinberg.longestWeyl F)
        (highestVector F .steinberg)) = polynomial F t := by
  change Steinberg.coordinates F
    (Steinberg.ambientAction F (unipotentProduct t * Steinberg.longestWeyl F)
      (Steinberg.seed F)) (0, 0, 1) = _
  unfold polynomial
  simp [Steinberg.seed, Steinberg.longestWeyl, unipotentProduct, map_mul,
    Module.End.mul_apply, Steinberg.e, pow_succ]
  ring_nf
  simp


private theorem coefficient_transport (σ : F ≃+* F) (g : Model F) :
    factorHighestCoefficient F .steinberg
      (action F .steinberg (fieldEquiv σ g) (highestVector F .steinberg)) =
    σ (factorHighestCoefficient F .steinberg
      (action F .steinberg g (highestVector F .steinberg))) := by
  change Steinberg.coordinates F
    (Steinberg.ambientAction F (fieldEquiv σ g) (Steinberg.seed F)) (0, 0, 1) =
    σ (Steinberg.coordinates F (Steinberg.ambientAction F g (Steinberg.seed F)) (0, 0, 1))
  have h : Steinberg.ambientAction F (fieldEquiv σ g) (Steinberg.seed F) =
      Steinberg.ambientCoefficientEquiv F σ
        (Steinberg.ambientAction F g (Steinberg.seed F)) := by
    calc
      _ = Steinberg.ambientAction F (fieldEquiv σ g)
          (Steinberg.ambientCoefficientEquiv F σ (Steinberg.seed F)) := by
        rw [Steinberg.ambientCoefficientEquiv_seed]
      _ = _ := Steinberg.ambientAction_fieldEquiv F σ g _
  rw [h]
  simp [Steinberg.seed]

variable [Finite F]
private theorem coefficient_frobenius (r : ℕ) (g : Model F) :
    factorHighestCoefficient F .steinberg
      (factorRep F r .steinberg g (highestVector F .steinberg)) =
    (factorHighestCoefficient F .steinberg
      (action F .steinberg g (highestVector F .steinberg))) ^ (2 ^ r) := by
  change factorHighestCoefficient F .steinberg
    (action F .steinberg (fieldEquiv (iterateFrobeniusEquiv F 2 r) g)
      (highestVector F .steinberg)) = _
  rw [coefficient_transport, iterateFrobeniusEquiv_apply, iterateFrobenius_def]

/-- The coefficient of a consecutive Steinberg Frobenius word is the indicated
power of the coefficient of its untwisted factor. -/
theorem word_coefficient (n r : ℕ) (g : Model F) :
    wordHighestCoefficient F (List.replicate n .steinberg)
      (wordRep F r (List.replicate n .steinberg) g
        (wordHighestVector F (List.replicate n .steinberg))) =
    (factorHighestCoefficient F .steinberg
      (action F .steinberg g (highestVector F .steinberg))) ^ (2 ^ r * (2 ^ n - 1)) := by
  induction n generalizing r with
  | zero => change (1 : F) = _; simp
  | succ n ih =>
    change factorHighestCoefficient F .steinberg
        (factorRep F r .steinberg g (highestVector F .steinberg)) *
      wordHighestCoefficient F (List.replicate n .steinberg)
        (wordRep F (r + 1) (List.replicate n .steinberg) g
          (wordHighestVector F (List.replicate n .steinberg))) = _
    rw [coefficient_frobenius, ih, ← pow_add]
    congr 1
    have hp : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
    have he : 2 ^ (n + 1) - 1 = 1 + 2 * (2 ^ n - 1) := by rw [pow_succ]; omega
    rw [he, pow_succ, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
end Atlas.G2.TensorClassification.FixedLine.SteinbergNormCalculation
end
