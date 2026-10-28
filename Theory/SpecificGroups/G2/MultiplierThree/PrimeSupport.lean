module

public import Theory.SpecificGroups.G2.MultiplierThree.Reduction
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Prime divisors of the G₂(3) universal kernel

The actual octonion model has order `2^6 * 3^6 * 7 * 13`. For every prime
other than two and three, its Sylow subgroups therefore have prime or trivial
order and are cyclic. Transfer excludes all these primes from every perfect
central kernel, in particular the literal canonical universal kernel.

Consequently the remaining upper-bound calculation is exactly the exclusion
of divisibility by two and by nine. Combining these two exclusions with the
proved prime support bounds the entire kernel order by three.

Source: Aschbacher–Smith I.1.2 and I.1.4(2), printed pp.407–408
(PDF pp.418–419); the standard G₂ order formula is the attributed ATLAS
port imported above (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

namespace Atlas.G2.FiniteCover.MultiplierThree
open PerfectCentralCovering

private theorem card_three_model : Nat.card (Model (ZMod 3)) = 2^6 * 3^6 * 7 * 13 := by
  rw [card_Model]
  norm_num

private theorem model_factorization_le_one {p : ℕ} (h2 : p ≠ 2) (h3 : p ≠ 3) :
    (Nat.card (Model (ZMod 3))).factorization p ≤ 1 := by
  rw [card_three_model]
  have hp7 : Nat.Prime 7 := by decide
  have hp13 : Nat.Prime 13 := by decide
  rw [Nat.factorization_mul (a := 2^6 * 3^6 * 7) (b := 13) (by decide) (by decide),
    Nat.factorization_mul (a := 2^6 * 3^6) (b := 7) (by decide) (by decide),
    Nat.factorization_mul (a := 2^6) (b := 3^6) (by decide) (by decide),
    Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization,
    hp7.factorization, hp13.factorization]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply,
    Ne.symm h2, Ne.symm h3, if_false, smul_eq_mul, mul_zero, zero_add]
  split_ifs <;> omega

/-- Away from two and three, each Sylow subgroup of the actual G₂(3) is cyclic. -/
public theorem sylow_isCyclic_of_ne_two_three {p : ℕ} [Fact p.Prime]
    (h2 : p ≠ 2) (h3 : p ≠ 3) (P : Sylow p (Model (ZMod 3))) : IsCyclic P := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [P.card_eq_multiplicity]
  simpa using (pow_dvd_pow p (model_factorization_le_one h2 h3))

/-- Only two and three can divide the canonical finite universal kernel order. -/
public theorem kernel_prime_dvd_eq_two_or_three {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card (Kernel (ZMod 3))) : p = 2 ∨ p = 3 := by
  by_contra h
  have h2 : p ≠ 2 := fun he => h (Or.inl he)
  have h3 : p ≠ 3 := fun he => h (Or.inr he)
  let : Fact p.Prime := ⟨hp⟩
  exact (universalCover (Model (ZMod 3))).not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_ne_two_three h2 h3) hd

/-- The full upper bound reduces to the two remaining primary calculations. -/
public theorem kernel_card_le_three_of_not_two_not_nine
    (h2 : ¬ 2 ∣ Nat.card (Kernel (ZMod 3)))
    (h9 : ¬ 9 ∣ Nat.card (Kernel (ZMod 3))) :
    Nat.card (Kernel (ZMod 3)) ≤ 3 := by
  have hdiv : Nat.card (Kernel (ZMod 3)) ∣ 3 := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd 3 _).mpr
    intro p k hp hpk
    by_cases hk : k = 0
    · subst k
      simp
    have hpd : p ∣ Nat.card (Kernel (ZMod 3)) := (dvd_pow_self p hk).trans hpk
    have hp3 : p = 3 := (kernel_prime_dvd_eq_two_or_three hp hpd).resolve_left
      (fun he => h2 (he ▸ hpd))
    subst p
    have hle : k ≤ 1 := by
      by_contra h
      exact h9 ((pow_dvd_pow 3 (by omega : 2 ≤ k)).trans hpk)
    simpa using pow_dvd_pow 3 hle
  exact Nat.le_of_dvd (by decide) hdiv

end Atlas.G2.FiniteCover.MultiplierThree
