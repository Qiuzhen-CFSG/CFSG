module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Configurations
public import Theory.GroupTheory.PerfectCentralCoverTorusNormalizer

/-!
# Lifting the odd Ree local configurations

A swapping or partial-inversion action forces lifts of two commuting
odd-order elements to commute. Thus the full preimage of the corresponding
abelian Sylow subgroup is abelian, and central transfer excludes its prime
from a perfect central kernel. At three, the additional torus inverter fixes
the cyclic supplement and inverts the derived subgroup of its full preimage;
the same transfer excludes three, at every torus exponent.

These deductions are conditional on the concrete configurations defined in
`Configurations`. They do not assert their existence on the Ree carrier.
The consumer in `OddPrimary` supplies precisely the local-section contract
used by `PrimaryReduction`, retaining the geometric premises explicitly.

Source: the central transfer calculation underlying Aschbacher–Smith
I.1.1–4, printed pp.407–408, and GLS3 §6.1.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary

open Subgroup PerfectCentralCovering
open scoped IsMulCommutative

variable {m p : ℕ} [Fact p.Prime]

private theorem sylow_card_coprime_two (hp : p ≠ 2) (P : Sylow p (Model m)) :
    (Nat.card P).Coprime 2 := by
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  rw [hk]
  apply Nat.Coprime.pow_left
  exact (Nat.coprime_primes (Fact.out : p.Prime) Nat.prime_two).mpr hp

/-- The geometric pair action makes the entire Sylow preimage abelian;
perfectness is not needed for this lifting calculation. -/
theorem AbelianSylowData.comap_isMulCommutative
    (D : AbelianSylowData m p) (hp : p ≠ 2)
    {E : Type*} [Group E] (f : E →* Model m)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    IsMulCommutative ((D.sylow : Subgroup (Model m)).comap f) := by
  have hxmem : D.first ∈ (D.sylow : Subgroup (Model m)) := by
    rw [← D.generated]
    exact subset_closure (by simp)
  have hx : D.first ^ Nat.card D.sylow = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨D.first, hxmem⟩ : D.sylow)))
  obtain ⟨a, ha⟩ := hf D.first
  obtain ⟨b, hb⟩ := hf D.second
  have hab : Commute a b := by
    rcases D.reverses with ⟨r, hrx, hry⟩ | ⟨r, hrx, hry⟩
    · exact CentralExtension.commute_lifts_of_swap f hf hk D.first D.second r
        (sylow_card_coprime_two hp D.sylow) hx D.generators_commute hrx hry a b ha hb
    · exact CentralExtension.commute_lifts_of_partial_inversion f hf hk D.first D.second r
        (sylow_card_coprime_two hp D.sylow) hx D.generators_commute hrx hry a b ha hb
  exact CentralExtension.isMulCommutative_comap_of_pair_lifts f hk D.sylow a b hab
    (by simpa only [ha, hb] using D.generated)

/-- The abelian configurations exclude the prime from every finite perfect
central kernel, without a prime-degree restriction. -/
theorem AbelianSylowData.not_dvd_kernel
    (D : AbelianSylowData m p) (hp : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  let : Group.IsPerfect E := c.isPerfect
  exact not_dvd_card_kernel_of_abelian_sylow_preimage c.toMonoidHom c.surjective
    c.ker_le_center D.sylow
    (D.comap_isMulCommutative hp c.toMonoidHom c.surjective c.ker_le_center)

/-- Both cyclic and rank-two torus configurations have the same kernel
consequence. All ambient equations are retained in the latter case. -/
theorem GoodPrimeGeometry.not_dvd_kernel
    (h : GoodPrimeGeometry m p) (hp : p ≠ 2)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  rcases h with hcyclic | hpair
  · exact c.not_dvd_card_multiplier_of_isCyclic_sylow hcyclic
  · obtain ⟨D⟩ := hpair
    exact D.not_dvd_kernel hp c

/-- The torus-plus-cycle configuration excludes three even when its torus
generators have order greater than three. -/
theorem ThreeSylowData.not_three_dvd_kernel
    (D : ThreeSylowData m)
    {E : Type*} [Group E] [Finite E] (c : Cover E (Model m)) :
    ¬ 3 ∣ Nat.card c.toMonoidHom.ker := by
  let : Group.IsPerfect E := c.isPerfect
  exact not_dvd_card_kernel_of_swapped_torus_normalizer
    c.toMonoidHom c.surjective c.ker_le_center (by decide : 3 ≠ 2)
    D.sylow D.torus D.first D.second D.cycle D.inverter D.swap
    D.torus_generated D.generators_commute D.swap_first D.swap_second
    D.sylow_generated D.cycle_normalizes D.inverts_torus D.fixes_cycle

/-- Primes absent from the model order require no torus construction. -/
theorem goodPrimeGeometry_of_not_dvd_card (h : ¬ p ∣ Nat.card (Model m)) :
    GoodPrimeGeometry m p := by
  left
  intro P
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd h, pow_zero]
  exact one_dvd p

end ReeF4.CentralCovers.OddPrimary
