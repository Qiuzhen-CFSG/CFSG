module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SimplePowerExtension
public import Theory.GroupTheory.AlternatingPowerTwoExtension
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The A6 quotient excludes the chi-zero blocks

A short subnormal subgroup of a two-group extension of an A6 power has
quotient A6 by its own two-core. Its order 360 is incompatible with all
three chi-zero quotient models. This excludes every such block, and hence
also all those moved by J(S), in the eventual hexad local overgroup.

The normal layer and its quotient maps are explicit hypotheses; their
construction from the orbit of the M22 component is a separate obligation.
Source: Aschbacher–Smith C.1.7, C.1.12 and 2.3.9(7)(f), printed pp.123–124
and 525–526 (combined manuscript of 1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup ChapterC Theory.GroupTheory

/-- The A6 quotient order cannot occur for an actual chi-zero block. -/
theorem not_chiZero_of_quotient_card_360 {K : Type*} [Group K]
    (hq : Nat.card (K ⧸ pCore 2 K) = 360) : ¬ IsChiZeroBlock K := by
  intro h
  rcases LieType.chiZero_order_module h with ⟨n, hn, he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · have hn3 : n < 3 := by
      by_contra hn3
      have hl : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      have hr : 2 ^ 6 ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
      have hp := Nat.mul_le_mul hl (Nat.sub_le_sub_right hr 1)
      rw [← he, hq] at hp
      norm_num at hp
    interval_cases n
    norm_num [hq] at he
  · omega
  · omega

/-- Subnormality in the actual local group excludes all chi-zero blocks. -/
theorem not_chiZeroBlockIn_of_a6PowerTwoExtension {K : Type*} [Group K]
    (hK : AlternatingPowerTwoExtension K 6) (B : Subgroup K) :
    ¬ IsChiZeroBlockIn B := by
  intro hB
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have htwo : ¬ IsPGroup 2 (alternatingGroup (Fin 6)) := by
    intro h
    obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
    rw [hcard] at hn
    have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 360).trans hn
    have := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at this
  obtain ⟨N, hN, hquot, n, f, hf, hker⟩ := hK
  let := hN
  obtain ⟨e⟩ := hB.1.quotient_equiv_of_simple_power
    (alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 6)))
    htwo N hquot f hf hker
  exact not_chiZero_of_quotient_card_360
    ((Nat.card_congr e.toEquiv).trans hcard) hB.2

/-- The obstruction includes every block moved by the specified J(S),
because the stronger subnormal block exclusion already applies. -/
theorem blockObstruction_of_a6PowerTwoExtension {G : Type*} [Group G]
    (M S X : Subgroup G) (hX : AlternatingPowerTwoExtension X 6) :
    BlockObstruction M S X := by
  intro B hB _
  exact (not_chiZeroBlockIn_of_a6PowerTwoExtension hX B hB).elim

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
