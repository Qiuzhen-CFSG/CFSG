module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Cyclic Sylow primes in perfect covers of J₂

The checked carrier order is 2⁷ · 3³ · 5² · 7. Outside 2, 3 and 5 every
Sylow subgroup is cyclic, including the trivial Sylow subgroups at primes
absent from the order. Central Sylow transfer therefore excludes all these
primes from every finite perfect central kernel.

Source: Aschbacher–Smith I.1.1–I.1.3, printed p.407; GLS3 §6.1.
The three- and five-primary exclusions are supplied by `OddPrimary`.
-/

namespace Theory.SpecificGroups.J2HSMultipliers.J2
open Sporadic.LeechRelated.J2 PerfectCentralCovering

private theorem square_not_dvd_card_carrier {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ Nat.card Carrier := by
  intro h
  have hd : p ∣ Nat.card Carrier := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [ExceptionalParabolics.FirstParabolic.card_carrier,
    show 604800 = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7 by norm_num] at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)] at hd
  rcases hd with ((h2 | h3) | h5) | h7
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow h5))
  · subst p
    norm_num [ExceptionalParabolics.FirstParabolic.card_carrier] at h

public theorem sylow_isCyclic_of_ne_two_three_five {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (P : Sylow p Carrier) :
    IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_card_carrier Fact.out hp2 hp3 hp5
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup Carrier).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

/-- Every prime outside the three noncyclic Sylow primes is excluded. -/
public theorem not_dvd_card_kernel_of_ne_two_three_five
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Carrier) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_ne_two_three_five hp2 hp3 hp5)

end Theory.SpecificGroups.J2HSMultipliers.J2
