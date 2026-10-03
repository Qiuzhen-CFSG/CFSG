module

public import Theory.Character.ModularBlock.PrimeCongruence
public import Theory.Character.ModularBlock.PrimePowerIdempotentSupport

/-!
# Weak block orthogonality from an integral projector

An integral central idempotent selecting an ordinary congruence block gives
zero degree-weighted character sum at every nonidentity prime-power element.
The prime-power coefficient support theorem kills its coefficient at the
inverse element. Its character expansion and the nonzero group order give
the assertion. This separates the trace calculation from the construction
of the actual localized block projector.

Source: Brauer's weak block orthogonality, in the form used in the cyclic
block degree equation; Alperin--Brauer--Gorenstein, III.8 Proposition 5,
printed p.117, and Brauer--Tuan (1945), §2.
-/

public section
noncomputable section
open scoped BigOperators
namespace ModularBlock.PrimePowerBlockOrthogonality
open PrimeBlockConstruction

/-- Weak orthogonality for a block with a specified integral projector.
The existence of that projector is a separate theorem. -/
theorem degree_sum_eq_zero_of_projector
    {G R : Type*} [Group G] [Finite G]
    [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R]
    {p : ℕ} [Fact p.Prime] (d : PrimeCongruenceBlockData p G) (j : d.I)
    (f : R →+* ℂ) (hp : ¬ IsUnit (p : R))
    (e : MonoidAlgebra R G) (he : IsIdempotentElem e)
    (hc : e ∈ Set.center (MonoidAlgebra R G))
    (hcoeff : ∀ g : G, f (e.coeff g) = (Nat.card G : ℂ)⁻¹ *
      ∑ i ∈ d.blockOf j, d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk g⁻¹))
    (g : G) (hg : g ≠ 1) {a : ℕ} (hga : g ^ (p ^ a) = 1) :
    ∑ i ∈ d.blockOf j, d.chi i (ConjClasses.mk 1) * d.chi i (ConjClasses.mk g) = 0 := by
  have hz := CentralIdempotentSupport.coeff_inv_eq_zero_of_prime_power p hp e he hc g hg hga
  have ht := hcoeff g⁻¹
  rw [inv_inv, hz, map_zero] at ht
  exact (mul_eq_zero.mp ht.symm).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos.ne')))

end ModularBlock.PrimePowerBlockOrthogonality
