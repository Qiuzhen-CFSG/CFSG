module

public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.PrimaryBounds
public import Theory.SpecificGroups.J2HSMultipliers.J2UpperBound.OddLocal
public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion
public import Theory.GroupTheory.Covering

/-!
# Odd-primary exclusion for every perfect central cover of J₂

The actual Sylow three-subgroup has a simultaneous inverter, and the Sylow
five-subgroup has a partial inverter. Commutator lifting and central Sylow
transfer exclude both primes from a perfect central kernel. Cyclic-Sylow
transfer handles all other odd primes, so the entire kernel is a two-group.

The source application uses the literal quotient projection L → L/Z(L)
followed by an actual equivalence to the permutation model. This discharges
the J₂ odd-primary center premise needed by A.2.19. It does not assert the
still separate two-primary upper bound of the full multiplier calculation.

Source: Aschbacher–Smith I.1.1–I.1.3(1), printed p.407; GLS3 §6.1.
-/

namespace Theory.SpecificGroups.J2HSMultipliers.J2
open Sporadic.LeechRelated.J2 PerfectCentralCovering Subgroup Theory.GroupTheory

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

public theorem not_three_dvd_card_kernel (f : E →* Carrier)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 3 ∣ Nat.card f.ker := by
  obtain ⟨Q, x, y, r, hQ, hx, hy, hz, hxz, hyz, hrx, hry, hrz⟩ :=
    UpperBound.OddLocal.exists_three_configuration
  exact not_dvd_card_kernel_of_simultaneous_inversion f hf hk
    (by decide : Nat.Coprime 3 2) Q x y r hQ hx hy hz hxz hyz hrx hry hrz

public theorem not_five_dvd_card_kernel (f : E →* Carrier)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 5 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨Q, x, y, r, hQ, hx, hxy, hrx, hry⟩ :=
    UpperBound.OddLocal.exists_five_configuration
  exact CentralExtension.not_dvd_card_kernel_of_partial_inversion f hf hk
    Q x y r hQ (by decide : Nat.Coprime 5 2) hx hxy hrx hry

/-- All finite perfect central kernels over the actual J₂ carrier are two-groups. -/
public theorem kernel_isPGroup (f : E →* Carrier)
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
    exact not_dvd_card_kernel_of_ne_two_three_five f hf hk hp'.1 h2 h3 h5 hp'.2.1
  norm_num [heq]

/-- Individually named exclusion for every odd prime, including primes absent from J₂. -/
public theorem not_odd_prime_dvd_card_kernel (f : E →* Carrier)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card f.ker := by
  obtain ⟨n, hn⟩ := (kernel_isPGroup f hf hk).exists_card_eq
  intro hd
  rw [hn] at hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))

public theorem kernel_eq_bot_of_odd_pGroup (f : E →* Carrier)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hkp : IsPGroup p f.ker) : f.ker = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  rcases hkp.card_eq_or_dvd with h | h
  · exact Subgroup.card_eq_one.mp h
  · exact (not_odd_prime_dvd_card_kernel f hf hk hp hp2 h).elim

/-- Apply the theorem to the literal quotient map followed by the supplied model equivalence. -/
public theorem center_isPGroup_of_quotient_equiv
    {L : Type*} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* Carrier) : IsPGroup 2 (center L) := by
  let f : L →* Carrier := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact (kernel_isPGroup f hf (le_of_eq hk)).of_equiv (MulEquiv.subgroupCongr hk)

/-- The quasisimple source form consumed by the sporadic A.2.19 branch. -/
public theorem source_center_isPGroup
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (h : Nonempty (L ⧸ center L ≃* Carrier)) : IsPGroup 2 (center L) := by
  obtain ⟨e⟩ := h
  exact center_isPGroup_of_quotient_equiv e

end Theory.SpecificGroups.J2HSMultipliers.J2
