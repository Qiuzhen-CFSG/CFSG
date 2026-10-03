module

public import Theory.Character.ModularBlock.CyclicFiveData
public import Theory.Character.ModularBlock.FiveSelfCentralizing
public import Theory.Character.ModularBlock.PrimePowerDegree
public import Theory.Character.DefectZeroVanishing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Nonvanishing and block membership for cyclic five-blocks

A principal-block row cannot vanish on the punctured order-five Sylow
subgroup: subgroup averaging and central-character congruences would make
the principal degree divisible by five. Conversely nonvanishing excludes
defect zero and hence forces degree prime to five. Together with
`FiveSelfCentralizing`, these facts identify nonzero rows with the block.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `CyclicSevenRows`.
-/

public section
noncomputable section
namespace ModularBlock.CyclicFive
open PrimeBlockConstruction
variable {G : Type*} [Group G] [Finite G]

private theorem ofConj_irreducible {χ : ConjClassFunction G}
    (hχ : IsIrreducibleConjCharacter χ) :
    IsIrreducibleCharacter (ofConjClassFunction χ) := by
  obtain ⟨n, ρ, hρ⟩ := hχ.1
  refine ⟨n, ρ, (irreducible_iff_character_norm_one ρ).mpr ?_, ?_⟩
  · simpa [hρ] using hχ.2
  · rw [hρ]
    rfl

/-- A principal-block row cannot vanish on the punctured Sylow subgroup. -/
theorem exists_value_ne_zero_of_mem_block (d : PrimeCongruenceBlockData 5 G)
    (P : Sylow 5 G) (hP : Nat.card P = 5) (i : d.I) (hi : i ∈ d.block) :
    ∃ u : P, u ≠ 1 ∧ d.chi i (ConjClasses.mk (u : G)) ≠ 0 := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let : CommGroup P := IsCyclic.commGroup
  by_contra h
  have hv : ∀ u : P, u ≠ 1 → d.chi i (ConjClasses.mk (u : G)) = 0 := by
    simpa only [not_exists, not_and, not_not] using h
  have hclass (u : P) : ¬ 5 ∣ Nat.card (ConjClasses.mk (u : G)).carrier := by
    have hle : (P : Subgroup G) ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
      intro x hx
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : P) u)
    rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
    exact fun h => P.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hle))
  have hprincipal : d.principal ∈ d.blockOf i := by
    rw [d.mem_blockOf_iff]
    exact ((d.mem_blockOf_iff i d.principal).mp hi).symm
  obtain ⟨n, hn, hdiv⟩ := d.degree_dvd_of_subgroup_vanishing i (P : Subgroup G)
    (by rw [hP]) (fun u _ => hclass u) hv d.principal hprincipal
  have hn1 : n = 1 := by
    have hc : (1 : ℂ) = (n : ℂ) := by simpa [d.principal_eq] using hn
    exact_mod_cast hc.symm
  subst n
  norm_num at hdiv

/-- Nonvanishing in an order-five Sylow subgroup excludes defect zero. -/
theorem degree_prime_to_five_of_value_ne_zero
    (d : PrimeCongruenceBlockData 5 G) (P : Sylow 5 G) (hP : Nat.card P = 5)
    (i : d.I) (n : ℕ) (hn : d.chi i (ConjClasses.mk 1) = (n : ℂ))
    (u : P) (hu : u ≠ 1) (hv : d.chi i (ConjClasses.mk (u : G)) ≠ 0) :
    ¬ 5 ∣ n := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hord : orderOf u = 5 := by
    have hcard : Nat.card ↥P = 5 := hP
    have hdiv : orderOf u ∣ 5 := by simpa only [hcard] using orderOf_dvd_natCard u
    exact ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdiv).resolve_left
      (fun h => hu (orderOf_eq_one_iff.mp h))
  intro hdiv
  apply hv
  exact OrdinaryCharacter.value_eq_zero_of_sylow_card_dvd_degree P
    (ofConj_irreducible (d.complete.1 i)) hn (by simpa only [hP] using hdiv) (u : G)
    (by rw [Subgroup.orderOf_coe, hord])

end ModularBlock.CyclicFive
