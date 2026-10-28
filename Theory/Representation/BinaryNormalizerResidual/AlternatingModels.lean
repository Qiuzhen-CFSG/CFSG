module
public import Theory.Representation.BinaryNormalizerResidual.AlternatingNatural
public import Theory.Representation.BinaryNormalizerResidual.FourDimensionalAlternating

/-!
# Small natural alternating model normalizer residuals

The five-, seven- and eight-letter scalar-commutant argument combines
with the faithful four-dimensional A₆ calculation to give the literal
normalizer residual bound for every natural alternating row in the
small-plane action list. The imported four-dimensional theorem also
covers the distinct A₇ four-space and exact Sp₄(2)′ natural action.

Source application: Aschbacher–Smith 13.7.6, printed p.940, with the
model markings retained from B.4.2 and B.5.1.
-/

public section
namespace Representation.BinaryNormalizerResidual
open Subgroup BinaryOffender BinaryPermutation

theorem alternating_small_natural_residual_le (n : ℕ)
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    (pResidual 2 (linearNormalizer (alternatingNaturalRepresentation (Ω := Fin n)))).map
      (linearNormalizer (alternatingNaturalRepresentation (Ω := Fin n))).subtype ≤
      actionImage (alternatingNaturalRepresentation (Ω := Fin n)) := by
  rcases hn with rfl | rfl | rfl | rfl
  · exact alternating_natural_residual_le 5 (Or.inl rfl)
  · apply alternatingSix_four_residual_le _ _ (MulEquiv.refl _)
    · simpa using finrank_natural_even (Fin 6) (by decide)
    · intro g h he
      apply Subtype.ext
      exact naturalRepresentation_injective (Fin 6) (by decide) he
  · exact alternating_natural_residual_le 7 (Or.inr (Or.inl rfl))
  · exact alternating_natural_residual_le 8 (Or.inr (Or.inr rfl))
end Representation.BinaryNormalizerResidual
