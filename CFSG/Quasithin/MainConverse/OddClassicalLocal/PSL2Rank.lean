module

public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankCubeFree
public import GorensteinWalter.PSL2CoprimeSylowCyclic
public import GorensteinWalter.PSL2DefiningPSubgroupCard
public import GorensteinWalter.PSL2Cardinality

/-!
# Odd-prime ranks of PSL₂ over prime fields

For a prime p ≥ 7, the defining-prime Sylow subgroups of PSL₂(p) have order p,
and all other odd Sylow subgroups are cyclic by the split/nonsplit torus
calculation. Their odd ranks are at most one. At p = 5, the order 60 has no
odd prime cube, which suffices for the rank bound two. Subgroup monotonicity
therefore proves QT for every prime p ≥ 5, without a Fermat–Mersenne restriction.

Source: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482; the Sylow
calculations are Huppert II.8.2–5. This establishes the QT clause only.
-/

namespace CFSG.Quasithin.MainConverse

open BenderSuzuki.MatrixGroups GorensteinWalter

/-- The prime-field PSL₂ groups in the source range are strongly quasithin. -/
public theorem psl2_prime_stronglyQuasithin (F : Type*) [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hp5 : 5 ≤ p) :
    IsStronglyQuasithin (PSL2MatrixGroup F) := by
  have hp : p.Prime := Fact.out
  have hFpow : Nat.card F = p ^ 1 := by simpa using hF
  by_cases hp7 : 7 ≤ p
  · intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    let R : Sylow r (PSL2MatrixGroup F) := default
    apply (R.primeRank_le_one_of_isCyclic ?_).trans (by decide)
    by_cases hrp : r = p
    · subst r
      exact isCyclic_of_card_dvd_prime (hF ▸
        psl2_defining_pgroup_card_dvd_field F hFpow R R.isPGroup')
    · exact psl2_sylow_isCyclic_of_coprime_field_card F hFpow (hF ▸ hp7)
        r (by intro he; subst r; exact ho.not_two_dvd_nat (dvd_refl 2))
        (hF ▸ (Nat.coprime_primes hr hp).mpr hrp) R
  · have hpodd := hp.odd_of_ne_two (by omega)
    have hpval : p = 5 := by obtain ⟨k, hk⟩ := hpodd; omega
    have hodd : IsOddPrimePower (Nat.card F) :=
      ⟨p, 1, hp, hpodd, by decide, hFpow⟩
    have hc : Nat.card (PSL2MatrixGroup F) = 60 := by
      rw [psl2_card_formula F hodd, hF, hpval]
      norm_num
    intro r hr ho
    let : Fact r.Prime := ⟨hr⟩
    apply primeRank_le_two_of_cube_not_dvd
    rw [hc]
    intro hd
    have hrd : r ∣ 60 := (dvd_pow_self r (by decide : 3 ≠ 0)).trans hd
    have hrval : r = 2 ∨ r = 3 ∨ r = 5 := by
      have : r ∣ 2 * (2 * (3 * 5)) := by norm_num at hrd ⊢; exact hrd
      rcases hr.dvd_mul.mp this with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
      rcases hr.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h)
      rcases hr.dvd_mul.mp h with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h))
      · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by decide)).mp h))
    rcases hrval with rfl | rfl | rfl
    · exact ho.not_two_dvd_nat (dvd_refl 2)
    all_goals norm_num at hd

/-- QT transports along the actual projective matrix-group witness. -/
public theorem psl2_prime_quasithin_of_isPSL
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hG : ClassicalGroup.IsPSL G 2 p) : IsQuasithin G := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hG
  let : Fact p.Prime := ⟨hp⟩
  exact Theory.GroupTheory.isQuasithin_of_equiv e.symm
    (psl2_prime_stronglyQuasithin F hF hp5).quasithin

end CFSG.Quasithin.MainConverse
