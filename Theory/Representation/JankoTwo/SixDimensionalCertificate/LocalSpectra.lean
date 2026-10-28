module

public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.Irreducibility
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.WeightTraces
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicDivisibility
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.CubicExclusion
public import Theory.Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra.SepticSpectrum

/-!
# Local degree-six spectral calculations for the literal Hall--Janko group

Every faithful six-dimensional representation in characteristic two is
absolutely irreducible. Over an algebraically closed field, its actual
simultaneous weights for the specified order-five pair form exactly one of
patterns zero and one. Simultaneous decomposition and rotation first give four
patterns; the cubic plane calculation and scalar-commutator determinant
constraint exclude the other two. No weight decomposition or catalogue is an
input to the assembled result.

The same pattern determines traces on x^a*y^b and c*x^j, and the trace on r²
vanishes. The independent septic theorem gives trace one over any
characteristic-two field, under the explicit order-seven and power-conjugacy
hypotheses. Its application to the literal word a*b retains these group inputs.
Global class coverage, twisting and comparison with the marked F₄ module are
separate obligations of the full trace certificate.

Source: Aschbacher--Smith K.4.5, printed p.460; Hiss--Malle corrected Table 2.
See SixDimensionalCertificate/Source.md for the precise local proof route.
-/

public section

namespace Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
open Sporadic.LeechRelated.J2
open scoped BigOperators

variable {E U : Type*} [Field E] [AddCommGroup U] [Module E U]
  [CharP E 2] [IsAlgClosed E] [FiniteDimensional E U]

/-- The two surviving simultaneous spectra of every faithful degree-six action.
The decomposition and the cubic exclusion are both discharged here. -/
theorem two_patterns (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    (∀ w, weightMultiplicity ρ ζ w = Weights.pattern 0 w) ∨
      (∀ w, weightMultiplicity ρ ζ w = Weights.pattern 1 w) := by
  obtain ⟨i, hi⟩ := four_patterns ρ hρ hdim hζ
  rcases CubicExclusion.pattern_zero_or_one ρ hζ i hi with rfl | rfl
  · exact Or.inl hi
  · exact Or.inr hi

/-- One and the same surviving weight pattern gives all the local torus and
mixed traces. This is the spectral input to the global character comparison;
there is no assumed multiplicity, decomposition or module-recognition premise. -/
theorem exists_pattern_with_local_traces
    (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    ∃ i : Fin 4, (i = 0 ∨ i = 1) ∧
      (∀ w, weightMultiplicity ρ ζ w = Weights.pattern i w) ∧
      (∀ a b : ℕ, ρ.character (TraceGeometry.x ^ a * TraceGeometry.y ^ b) =
        ∑ w : Weights.Weight, (Weights.pattern i w : E) *
          ζ ^ (w.1.val * a + w.2.val * b)) ∧
      (∀ j : ℕ, ρ.character (TraceGeometry.c * TraceGeometry.x ^ j) =
        if i = 0 then 1 + ζ ^ j + ζ ^ (4 * j)
        else 1 + ζ ^ (2 * j) + ζ ^ (3 * j)) ∧
      ρ.character (TraceGeometry.r ^ 2) = 0 := by
  have hr := character_r_sq ρ hρ hdim hζ
  rcases two_patterns ρ hρ hdim hζ with hzero | hone
  · refine ⟨0, Or.inl rfl, hzero, character_torus_of_pattern ρ hζ 0 hzero, ?_, hr⟩
    intro j
    simpa using
      CubicExclusion.character_c_mul_x_pow_of_pattern_zero ρ hζ hzero j
  · refine ⟨1, Or.inr rfl, hone, character_torus_of_pattern ρ hζ 1 hone, ?_, hr⟩
    intro j
    simpa only [if_neg (show (1 : Fin 4) ≠ 0 by decide)] using
      CubicExclusion.character_c_mul_x_pow_of_pattern_one ρ hζ hone j

/-- Both surviving local spectra give trace one on the literal cubic. -/
theorem character_c (ρ : Representation E Carrier U) (hρ : Function.Injective ρ)
    (hdim : Module.finrank E U = 6) {ζ : E} (hζ : IsPrimitiveRoot ζ 5) :
    ρ.character TraceGeometry.c = 1 := by
  rcases two_patterns ρ hρ hdim hζ with hzero | hone
  · simpa only [pow_zero, mul_one, Nat.mul_zero, CharTwo.add_self_eq_zero, zero_add] using
      CubicExclusion.character_c_mul_x_pow_of_pattern_zero ρ hζ hzero 0
  · simpa only [pow_zero, mul_one, Nat.mul_zero, CharTwo.add_self_eq_zero, zero_add] using
      CubicExclusion.character_c_mul_x_pow_of_pattern_one ρ hζ hone 0

end Representation.JankoTwo.SixDimensionalCertificate.LocalSpectra
