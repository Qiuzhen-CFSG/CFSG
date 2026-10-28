module

public import Theory.SpecificGroups.Rudvalis.Multiplier.Perfect
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Prime divisors of Rudvalis perfect central kernels

The certified order is 2^14 * 3^3 * 5^3 * 7 * 13 * 29. Outside 2,3,5 every
Sylow subgroup is cyclic, so central Sylow transfer excludes that prime from
the kernel of any finite perfect central cover. Primes absent from the base
order are included. No quasisimplicity or intrinsic simplicity is required.
Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; the original ATLAS
order certificate is `Model.Order`.
-/

namespace Rudvalis.Multiplier
open PerfectCentralCovering

private theorem square_not_dvd_card_model {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ Nat.card Model := by
  intro h
  have hd : p ∣ Nat.card Model := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [model_card,
    show 145926144000 = 2 ^ 14 * 3 ^ 3 * 5 ^ 3 * 7 * 13 * 29 by norm_num] at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29)] at hd
  rcases hd with ((((h2 | h3) | h5) | h7) | h13) | h29
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow h5))
  · subst p
    norm_num [model_card] at h
  · subst p
    norm_num [model_card] at h
  · subst p
    norm_num [model_card] at h

public theorem sylow_isCyclic_of_ne_two_three_five {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (P : Sylow p Model) :
    IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_card_model Fact.out hp2 hp3 hp5
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup Model).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

public theorem not_dvd_card_kernel_of_ne_two_three_five
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_ne_two_three_five hp2 hp3 hp5)

end Rudvalis.Multiplier
