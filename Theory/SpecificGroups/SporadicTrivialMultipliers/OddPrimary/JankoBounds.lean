module

public import Theory.SpecificGroups.Janko4.Model
public import Theory.SpecificGroups.Janko4.Model.Cardinality.Thompson
public import Theory.GroupTheory.PerfectCentralCover

/-!
# Cyclic Sylow bounds for Janko4 perfect covers

The exact order shows every Sylow subgroup outside 2, 3 and 11 has prime
order or is trivial. Central Sylow transfer excludes those primes from any
finite perfect central kernel. The two nonabelian odd Sylow subgroups are
handled separately by their actual normalizer actions.
Source: Aschbacher–Smith I.1.3, printed p.407.
-/

namespace Janko4.OddPrimary
open PerfectCentralCovering

private theorem square_not_dvd_card_model {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp11 : p ≠ 11) :
    ¬ p ^ 2 ∣ Nat.card Model := by
  intro h
  have hd : p ∣ Nat.card Model := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [Cardinality.Thompson.model_card,
    show 86775571046077562880 = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 by norm_num] at hd
  simp only [hp.dvd_mul] at hd
  rcases hd with (((((((((h2 | h3) | h5) | h7) | h11) | h23) | h29) | h31) | h37) | h43)
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp h5
    subst p
    norm_num [Cardinality.Thompson.model_card] at h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h7
    subst p
    norm_num [Cardinality.Thompson.model_card] at h
  · exact hp11 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)).mp
      (hp.dvd_of_dvd_pow h11))
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 23)).mp h23
    subst p
    norm_num [Cardinality.Thompson.model_card] at h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 29)).mp h29
    subst p
    norm_num [Cardinality.Thompson.model_card] at h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)).mp h31
    subst p
    norm_num [Cardinality.Thompson.model_card] at h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 37)).mp h37
    subst p
    norm_num [Cardinality.Thompson.model_card] at h
  · have := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 43)).mp h43
    subst p
    norm_num [Cardinality.Thompson.model_card] at h

public theorem sylow_isCyclic_of_ne_two_three_eleven {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp11 : p ≠ 11) (P : Sylow p Model) :
    IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_card_model Fact.out hp2 hp3 hp11
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup Model).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

public theorem not_dvd_card_kernel_of_ne_two_three_eleven
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp11 : p ≠ 11) :
    ¬ p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_ne_two_three_eleven hp2 hp3 hp11)

end Janko4.OddPrimary
