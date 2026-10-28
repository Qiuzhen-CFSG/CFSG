module

public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldSeven
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldThree
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldFive
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.HeldBounds
public import Theory.GroupTheory.Covering

/-!
# Odd-primary exclusion for actual Held covers

The literal order-27 subgroup has a simultaneous inverter. Two explicit
commuting elements of order five have a partial inverter and generate the
full five-part. In the actual order-343 subgroup, a reciprocal scaling action
fixes the central commutator and makes both commutators of lifts vanish.
Central Sylow transfer excludes 3, 5 and 7. The proved odd-order bound and
cyclic Sylow transfer exclude all other odd primes.

Composing the center quotient with an equivalence to the concrete Held
carrier therefore proves the center is a two-group. This is the actual
source-domain upper bound for A.2.19 and A.3.6; no multiplier or local-Sylow
premise remains. It does not calculate the two-primary multiplier.
Source: Aschbacher–Smith I.1.3, printed p.407; GLS III Table 5.3p.
-/

namespace Held.OddPrimary
open PerfectCentralCovering Subgroup Theory.GroupTheory

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- The early upper bound: every finite perfect central kernel over Held is a two-group. -/
public theorem kernel_isPGroup (f : E →* He)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) : IsPGroup 2 f.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra h2
    by_cases h3 : p = 3
    · subst p
      exact not_three_dvd_card_kernel f hf hk hp'.2.1
    by_cases h5 : p = 5
    · subst p
      exact not_five_dvd_card_kernel f hf hk hp'.2.1
    by_cases h7 : p = 7
    · subst p
      exact not_seven_dvd_card_kernel f hf hk hp'.2.1
    exact not_dvd_card_kernel_of_ne_two_three_five_seven f hf hk hp'.1 h2 h3 h5 h7 hp'.2.1
  norm_num [heq]

/-- A nontrivial odd prime-power central kernel cannot occur over the actual Held carrier. -/
public theorem kernel_eq_bot_of_odd_pGroup (f : E →* He)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hkp : IsPGroup p f.ker) : f.ker = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hk2 := kernel_isPGroup f hf hk
  obtain ⟨n, hn⟩ := hk2.exists_card_eq
  rcases hkp.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · rw [hn] at h
    exact (hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow h))).elim

/-- The literal source-cover application: compose L → L/Z(L) with its actual model equivalence. -/
public theorem center_isPGroup_of_quotient_equiv
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* He) : IsPGroup 2 (center L) := by
  let f : L →* He := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact (kernel_isPGroup f hf (le_of_eq hk)).of_equiv (MulEquiv.subgroupCongr hk)

/-- The actual center bound consumed by A.2.19 and A.3.6. -/
public theorem source_center_isPGroup
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (h : Nonempty (L ⧸ center L ≃* He)) : IsPGroup 2 (center L) := by
  obtain ⟨e⟩ := h
  exact center_isPGroup_of_quotient_equiv e

end Held.OddPrimary
