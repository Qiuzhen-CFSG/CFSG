module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OutsideStructure.Uniqueness
public import Mathlib.GroupTheory.Nilpotent

/-!
# Sylow containment for the outside-overgroup argument

If `S` has index two in a Sylow two-subgroup and `N_G(S) ≤ M`, every
two-subgroup containing `S` lies in `M`. Indeed, a proper overgroup has a
strictly larger normalizer of `S`. Its order is then already at least the
order of an ambient Sylow subgroup, so it is the entire overgroup.

This supplies the first step of Aschbacher–Smith 15.3.11(1), printed p.1124
in the combined manuscript (1 March 2004). The remaining step excludes a
full Sylow subgroup using 15.3.2(4).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.OutsideStructure
variable {G : Type*} [Group G] [Finite G]
/-- Index-two Sylow size and normalizer control contain every two-overgroup. -/
theorem two_overgroup_le_of_index_two (T : Sylow 2 G) (S M P : Subgroup G)
    (hST : S ≤ (T : Subgroup G))
    (hindex : (S.subgroupOf (T : Subgroup G)).index = 2)
    (hNM : normalizer (S : Set G) ≤ M)
    (hP : IsPGroup 2 P) (hSP : S ≤ P) : P ≤ M := by
  by_cases heq : P = S
  · exact heq ▸ (S.le_normalizer.trans hNM)
  let : Group.IsNilpotent P := hP.isNilpotent
  have hproper : S.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, subgroupOf_eq_top]
    exact fun hPS => heq (le_antisymm hPS hSP)
  obtain ⟨x, hxN, hxS⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (S.subgroupOf P) hproper)
  have hx : (x : G) ∈ normalizer (S : Set G) := by
    rw [← subgroupOf_normalizer_eq hSP] at hxN
    exact hxN
  let N := P ⊓ normalizer (S : Set G)
  have hSN : S ≤ N := le_inf hSP S.le_normalizer
  have hnotone : (S.subgroupOf N).index ≠ 1 := by
    intro hi
    have he := index_eq_one.mp hi
    have hm : (⟨x, ⟨x.property, hx⟩⟩ : N) ∈ S.subgroupOf N := he ▸ mem_top _
    exact hxS hm
  have htwo : 2 ≤ (S.subgroupOf N).index := by
    have hpos := (S.subgroupOf N).index_ne_zero_of_finite
    omega
  have hNc : Nat.card S * (S.subgroupOf N).index = Nat.card N := by
    simpa only [Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv] using
      (S.subgroupOf N).card_mul_index
  have hTc : Nat.card S * 2 = Nat.card T := by
    simpa only [hindex, Nat.card_congr (subgroupOfEquivOfLe hST).toEquiv] using
      (S.subgroupOf (T : Subgroup G)).card_mul_index
  obtain ⟨U, hPU⟩ := hP.exists_le_sylow
  have hPc : Nat.card P ≤ Nat.card T := by
    calc
      Nat.card P ≤ Nat.card U := card_le_of_le hPU
      _ = Nat.card T := by rw [U.card_eq_multiplicity, T.card_eq_multiplicity]
  have hPN : P = N := eq_of_le_of_card_ge (show N ≤ P from inf_le_left) (by
    calc
      Nat.card P ≤ Nat.card T := hPc
      _ = Nat.card S * 2 := hTc.symm
      _ ≤ Nat.card S * (S.subgroupOf N).index := Nat.mul_le_mul_left _ htwo
      _ = Nat.card N := hNc) |>.symm
  exact hPN ▸ (inf_le_right.trans hNM)
end CFSG.Quasithin.Chapter15.Section03.OutsideStructure

end
