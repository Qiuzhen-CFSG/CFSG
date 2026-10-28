module

public import Theory.GroupTheory.SolvablePrimeNormalizer
public import Theory.SpecificGroups.Janko1.Model.SylowTwo

/-!
# The local normalizer bounds needed for the J₁ solvable-overgroup argument

The concrete matrix group has elementary abelian Sylow two-subgroups of
order eight, and its odd prime factors occur only once. Consequently the
normalizer bounds for subgroups of orders 3, 5, 7, 11 and 19 are precisely
the additional inputs needed by the solvable Fitting argument.

`PrimeNormalizerBound p` asserts an actual order restriction on the
normalizer of every subgroup of order p in `Janko1.Model`. The theorem below
is conditional on these local bounds; their concrete verification remains
necessary to complete the source argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.510; GLS3 Table 5.3f, with odd-prime normalizer orders 60, 60, 42, 110, 114.
-/

namespace Janko1.LocalStructure
open Subgroup

/-- A prime-order subgroup normalizer cannot contain a Sylow two-subgroup
of the actual J₁ matrix group. -/
@[expose] public def PrimeNormalizerBound (p : ℕ) : Prop :=
  ∀ A : Subgroup Model, Nat.card A = p → ¬ 8 ∣ Nat.card (normalizer (A : Set Model))

private theorem odd_prime_cases {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hd : p ∣ Nat.card Model) : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
  rw [card_model] at hd
  change p ∣ 2 * 2 * 2 * 3 * 5 * 7 * 11 * 19 at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 19)] at hd
  have h2 : p ≠ 2 := fun he => ho.not_two_dvd_nat (he ▸ dvd_rfl)
  omega

/-- The five odd primes dividing the certified order suffice for all
odd-prime normalizer bounds. -/
public theorem primeNormalizerBound_of_cases
    (h3 : PrimeNormalizerBound 3) (h5 : PrimeNormalizerBound 5)
    (h7 : PrimeNormalizerBound 7) (h11 : PrimeNormalizerBound 11)
    (h19 : PrimeNormalizerBound 19) {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    PrimeNormalizerBound p := by
  intro A hA
  have hd : p ∣ Nat.card Model := hA ▸ A.card_subgroup_dvd_card
  rcases odd_prime_cases hp ho hd with rfl | rfl | rfl | rfl | rfl
  · exact h3 A hA
  · exact h5 A hA
  · exact h7 A hA
  · exact h11 A hA
  · exact h19 A hA

/-- The genuine prime-normalizer bounds force normalization in every
solvable overgroup of a Sylow two-subgroup. -/
public theorem solvable_overgroup_le_normalizer_of_prime_bounds
    (hN : ∀ p : ℕ, p.Prime → Odd p → PrimeNormalizerBound p)
    (S : Sylow 2 Model) (H : Subgroup Model) [Group.IsSolvable H]
    (hSH : (S : Subgroup Model) ≤ H) : H ≤ normalizer (S : Set Model) := by
  let _ := SylowTwo.elementary S
  apply solvable_overgroup_le_normalizer_of_prime_normalizers S ?_ ?_ H hSH
  · intro p hp hne hd
    have hpd : p ∣ Nat.card Model := (show p ∣ p ^ 2 from ⟨p, by simp [pow_two]⟩).trans hd
    rcases odd_prime_cases hp (hp.odd_of_ne_two hne) hpd with rfl | rfl | rfl | rfl | rfl <;>
      norm_num [card_model] at hd
  · intro p hp hne A hA
    rw [SylowTwo.card S]
    exact hN p hp (hp.odd_of_ne_two hne) A hA

end Janko1.LocalStructure
