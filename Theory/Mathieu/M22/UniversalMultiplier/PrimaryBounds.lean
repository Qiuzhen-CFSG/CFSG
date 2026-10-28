module

public import Theory.Mathieu.M22.Properties.Order
public import Theory.GroupTheory.PerfectCentralCoverSylowNine

/-!
# Odd-primary bounds for central coverings of M₂₂

The certified order of the actual degree-22 group is
`2^7 * 3^2 * 5 * 7 * 11`. Outside two and three its Sylow subgroups are
cyclic, so central Sylow transfer excludes those primes from a perfect
central kernel. The Sylow-nine bound excludes a second factor of three.
Consequently an independent exclusion of eight from the kernel order gives
the full upper bound twelve.

These are upper-bound steps for Aschbacher–Smith I.1.3(4), printed p.407.
They do not construct the required cyclic-four cover or prove its existence.
-/

namespace Sporadic.Mathieu.M22UniversalMultiplier

open PerfectCentralCovering

private theorem square_not_dvd_card {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ^ 2 ∣ Nat.card M22 := by
  intro h
  have hd : p ∣ Nat.card M22 := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [m22_order, show 443520 = 2 ^ 7 * 3 ^ 2 * 5 * 7 * 11 by norm_num] at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 11)] at hd
  rcases hd with (((h2 | h3) | h5) | h7) | h11
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
      (hp.dvd_of_dvd_pow h3))
  · subst p
    rw [m22_order] at h
    norm_num at h
  · subst p
    rw [m22_order] at h
    norm_num at h
  · subst p
    rw [m22_order] at h
    norm_num at h

/-- All Sylow subgroups away from two and three in the actual M₂₂ are cyclic. -/
public theorem sylow_isCyclic_of_ne_two_three {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (P : Sylow p M22) : IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    exact square_not_dvd_card Fact.out hp2 hp3
      ((pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup M22).card_subgroup_dvd_card))
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

/-- Only two and three can divide a finite perfect central kernel over M₂₂. -/
public theorem not_dvd_kernel_of_ne_two_three
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow
    (sylow_isCyclic_of_ne_two_three hp2 hp3)

/-- Three occurs at most once in any finite perfect central kernel over M₂₂. -/
public theorem not_nine_dvd_kernel
    {E : Type*} [Group E] [Finite E] (f : Cover E M22) :
    ¬ 9 ∣ Nat.card f.toMonoidHom.ker := by
  let P : Sylow 3 M22 := Classical.choice inferInstance
  apply f.not_nine_dvd_card_kernel_of_sylow_nine P
  rw [P.card_eq_multiplicity, m22_order]
  decide +kernel

/-- The remaining two-primary upper bound suffices for the complete order bound.
The exclusion of eight is an explicit independent obligation. -/
public theorem kernel_card_dvd_twelve_of_not_eight
    {E : Type*} [Group E] [Finite E] (f : Cover E M22)
    (h8 : ¬ 8 ∣ Nat.card f.toMonoidHom.ker) : Nat.card f.toMonoidHom.ker ∣ 12 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  have hpd : p ∣ Nat.card f.toMonoidHom.ker :=
    (dvd_pow_self p hk).trans hpk
  by_cases hp2 : p = 2
  · subst p
    have hk2 : k ≤ 2 := by
      by_contra! hn
      exact h8 ((pow_dvd_pow 2 hn).trans hpk)
    exact (pow_dvd_pow 2 hk2).trans (by decide : 2 ^ 2 ∣ 12)
  by_cases hp3 : p = 3
  · subst p
    have hk1 : k ≤ 1 := by
      by_contra! hn
      exact not_nine_dvd_kernel f ((pow_dvd_pow 3 hn).trans hpk)
    exact (pow_dvd_pow 3 hk1).trans (by decide : 3 ^ 1 ∣ 12)
  exact (not_dvd_kernel_of_ne_two_three f hp hp2 hp3 hpd).elim

end Sporadic.Mathieu.M22UniversalMultiplier
