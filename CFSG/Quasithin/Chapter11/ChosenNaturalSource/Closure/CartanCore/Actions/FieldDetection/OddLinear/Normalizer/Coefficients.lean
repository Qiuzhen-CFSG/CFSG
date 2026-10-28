module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Coefficients

/-!
# The odd subfield is fixed by two-power actors

The restriction of a two-power coefficient automorphism has order dividing
both a power of two and the odd subfield degree, hence is the identity.
The conclusion retains the original subfield inclusion. This is the
coefficient step in the simultaneous Sylow/subfield arrangement of
Aschbacher--Smith 11.5.6(3), printed p.781.
-/

public section
open Subgroup CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- Every two-power coefficient actor fixes the constructed odd-degree subfield. -/
theorem oddRestriction_eq_one_of_two_power (F : BinaryField)
    (σ : F.Carrier ≃+* F.Carrier) {k : ℕ} (hσ : σ ^ (2 ^ k) = 1) :
    oddRestriction F σ = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes ((oddSubfield_degree_odd F).coprime_two_left.pow_left k)
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hσ, map_one]
  · have hd := orderOf_dvd_natCard (oddRestriction F σ)
    rw [FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two (oddField F).card_eq] at hd
    exact hd

/-- Fixation is stated through the original inclusion, not a replacement field. -/
theorem oddInclusion_fixed_of_two_power (F : BinaryField)
    (σ : F.Carrier ≃+* F.Carrier) {k : ℕ} (hσ : σ ^ (2 ^ k) = 1)
    (u : (oddField F).Carrierˣ) :
    Units.map σ.toMonoidHom (Units.map (oddInclusion F).toMonoidHom u) =
      Units.map (oddInclusion F).toMonoidHom u := by
  apply Units.ext
  have h := oddRestriction_apply F σ u.val
  rw [oddRestriction_eq_one_of_two_power F σ hσ] at h
  exact h.symm
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
