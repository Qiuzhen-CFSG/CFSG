module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks

/-!
# Primary reductions for the G₂(4) universal kernel bound

The actual octonion group has order `2^12 * 3^3 * 5^2 * 7 * 13`.
Every Sylow subgroup outside the primes 2, 3 and 5 therefore has order
dividing its prime and is cyclic. Cyclic-Sylow transfer excludes all those
primes from the kernel of every finite perfect central cover, including
primes absent from the base group order.

For the literal canonical universal kernel this leaves precisely the
exclusions of 3 and 5 and the bound that 4 does not divide its order.
The final arithmetic reduction below consumes these three inputs; this
module does not yet assert the unconditional upper bound.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407 (PDF p.418),
and GLS III §6.1, Tables 6.1.2–6.1.3. The noncyclic-Sylow calculations
are the additional work in Griess, *Schur multipliers of finite simple
groups of Lie type*, Trans. AMS 183 (1973), 355–421; Steinberg,
*Generators, relations, and coverings of algebraic groups II*, §3.5,
explicitly refers the G₂ calculation to Griess, pp.357–371.
The imported octonion order formula retains its ATLAS attribution.
-/

namespace Atlas.G2.FiniteCover.MultiplierFourBound

open PerfectCentralCovering

private theorem square_not_dvd_card_base {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ Nat.card FourBase := by
  intro h
  have hd : p ∣ Nat.card FourBase := (dvd_pow_self p (by decide : 2 ≠ 0)).trans h
  rw [OrderChecks.four_order,
    show 251596800 = 2 ^ 12 * 3 ^ 3 * 5 ^ 2 * 7 * 13 by norm_num] at hd
  simp only [hp.dvd_mul,
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 13)] at hd
  rcases hd with (((h2 | h3) | h5) | h7) | h13
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2))
  · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h3))
  · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp
      (hp.dvd_of_dvd_pow h5))
  · subst p
    norm_num [OrderChecks.four_order] at h
  · subst p
    norm_num [OrderChecks.four_order] at h

private theorem sylow_isCyclic_of_square_not_dvd
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ¬ p ^ 2 ∣ Nat.card G) (P : Sylow p G) : IsCyclic P := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnle : n ≤ 1 := by
    by_contra! hh
    apply h
    exact (pow_dvd_pow p hh).trans (hn ▸ (P : Subgroup G).card_subgroup_dvd_card)
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [hn]
  simpa only [pow_one] using pow_dvd_pow p hnle

/-- The only possibly noncyclic Sylow subgroups have primes 2, 3 or 5. -/
public theorem sylow_isCyclic_of_ne_two_three_five {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) (P : Sylow p FourBase) :
    IsCyclic P :=
  sylow_isCyclic_of_square_not_dvd (square_not_dvd_card_base Fact.out hp2 hp3 hp5) P

/-- Transfer excludes every other prime from any finite perfect central kernel. -/
public theorem not_dvd_card_kernel_of_ne_two_three_five
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* FourBase) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ∣ Nat.card f.ker := by
  let : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_kernel_of_isCyclic_sylow f hf hk
    (sylow_isCyclic_of_ne_two_three_five hp2 hp3 hp5)

/-- Apply the transfer calculation to the prescribed universal projection. -/
public theorem not_dvd_card_universal_kernel_of_ne_two_three_five
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp5 : p ≠ 5) :
    ¬ p ∣ Nat.card (Kernel FourField) :=
  not_dvd_card_kernel_of_ne_two_three_five (universalProjection FourBase)
    (universalProjection_surjective FourBase) (universalProjection_ker_le_center FourBase)
    hp hp2 hp3 hp5

/-- The three remaining primary bounds imply the full bound, with no
unmentioned prime-divisor assumption on the universal kernel. -/
public theorem card_kernel_le_two_of_primary_bounds
    (h3 : ¬ 3 ∣ Nat.card (Kernel FourField))
    (h5 : ¬ 5 ∣ Nat.card (Kernel FourField))
    (h4 : ¬ 4 ∣ Nat.card (Kernel FourField)) :
    Nat.card (Kernel FourField) ≤ 2 := by
  apply Nat.le_of_dvd (by decide : 0 < 2)
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 2 _).mpr
  intro p k hp hpk
  by_cases hk : k = 0
  · simp [hk]
  have hd : p ∣ Nat.card (Kernel FourField) := (dvd_pow_self p hk).trans hpk
  have hp2 : p = 2 := by
    by_contra hp2
    by_cases hp3 : p = 3
    · subst p
      exact h3 hd
    by_cases hp5 : p = 5
    · subst p
      exact h5 hd
    exact not_dvd_card_universal_kernel_of_ne_two_three_five hp hp2 hp3 hp5 hd
  subst p
  have hle : k ≤ 1 := by
    by_contra! hh
    exact h4 ((pow_dvd_pow 2 hh).trans hpk)
  simpa only [pow_one] using pow_dvd_pow 2 hle

end Atlas.G2.FiniteCover.MultiplierFourBound
