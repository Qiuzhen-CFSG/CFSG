module

public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.JankoEleven
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.JankoThree
public import Theory.SpecificGroups.SporadicTrivialMultipliers.OddPrimary.JankoBounds
public import Theory.GroupTheory.Covering

/-!
# Odd-primary exclusion for actual Janko4 covers

The two certified nonabelian Sylow configurations exclude 3 and 11.
The exact order and cyclic Sylow transfer exclude every other odd prime.
Thus every finite perfect central cover has a two-group kernel. Composing
the literal center quotient with its supplied model equivalence gives the
source conclusion for any finite quasisimple group with quotient Janko4.
This upper bound does not assert the full trivial-multiplier theorem.

Source: Aschbacher–Smith I.1.3, printed p.407; A.2.19 and A.3.6.
-/

namespace Janko4.OddPrimary
open PerfectCentralCovering Subgroup Theory.GroupTheory

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]

/-- The early upper bound: every finite perfect central kernel over J4 is a two-group. -/
public theorem kernel_isPGroup (f : E →* Model)
    (hf : Function.Surjective f) (hk : f.ker ≤ center E) : IsPGroup 2 f.ker := by
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 2 ≠ 0)).mpr
  intro p hp
  have hp' := Nat.mem_primeFactors.mp hp
  have heq : p = 2 := by
    by_contra h2
    by_cases h3 : p = 3
    · subst p
      exact not_three_dvd_card_kernel f hf hk hp'.2.1
    by_cases h11 : p = 11
    · subst p
      exact not_eleven_dvd_card_kernel f hf hk hp'.2.1
    exact not_dvd_card_kernel_of_ne_two_three_eleven f hf hk hp'.1 h2 h3 h11 hp'.2.1
  norm_num [heq]

/-- A nontrivial odd prime-power central kernel cannot occur over the actual J4 carrier. -/
public theorem kernel_eq_bot_of_odd_pGroup (f : E →* Model)
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
    (e : L ⧸ center L ≃* Model) : IsPGroup 2 (center L) := by
  let f : L →* Model := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = center L := by
    dsimp [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact (kernel_isPGroup f hf (le_of_eq hk)).of_equiv (MulEquiv.subgroupCongr hk)

/-- Exact premise consumed by the direct K.4 Janko4 exclusion and A.2.19 assembly. -/
public theorem source_center_isPGroup
    {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    (h : Nonempty (L ⧸ center L ≃* Model)) : IsPGroup 2 (center L) := by
  obtain ⟨e⟩ := h
  exact center_isPGroup_of_quotient_equiv e

end Janko4.OddPrimary
