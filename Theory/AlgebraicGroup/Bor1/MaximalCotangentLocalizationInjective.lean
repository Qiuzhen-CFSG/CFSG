module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.AtPrime.Basic

universe u

namespace Theory.AlgebraicGroup.Bor1

open IsLocalRing

/-- The natural map on cotangent spaces induced by localization at a maximal
ideal is injective. -/
public theorem maximalCotangentLocalizationMap_injective
    (R : Type u) [CommRing R]
    (p : Ideal R) [p.IsMaximal]
    (Rₚ : Type u) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    (hcomp : p ≤ (maximalIdeal Rₚ).comap (Algebra.ofId R Rₚ)) :
    Function.Injective
      (Ideal.mapCotangent p (maximalIdeal Rₚ)
        (Algebra.ofId R Rₚ) hcomp) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨x, rfl⟩ := p.toCotangent_surjective z
  rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq_zero] at hz
  rw [Ideal.toCotangent_eq_zero]
  rw [← IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ 2,
    Ideal.mem_under]
  exact hz

end Theory.AlgebraicGroup.Bor1
