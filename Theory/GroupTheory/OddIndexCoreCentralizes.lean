module

public import Theory.GroupTheory.CenterFreeOddImageCore

/-!
# Collapse under an odd-index action

Suppose an acting group has a normal two-subgroup of odd index which
centralizes a normalized solvable two-subgroup. If the full acting group
has no fixed points there, a bound on its commutator bounds the subgroup
itself. Schur–Zassenhaus supplies an odd complement, and the existing
coprime decomposition identifies the subgroup with its commutator.

The acting group need not contain the module subgroup. Neither the
commutator bound nor the module is assumed normal in the ambient group.
-/


namespace Subgroup

public theorem le_of_odd_index_core_centralizes
    {G : Type*} [Group G] [Finite G]
    (acting core moduleSubgroup bound : Subgroup G)
    (hcore : core ≤ acting) [(core.subgroupOf acting).Normal]
    (htwoCore : IsPGroup 2 core)
    (hodd : Odd (core.subgroupOf acting).index)
    (htwoModule : IsPGroup 2 moduleSubgroup)
    (hsolvable : Group.IsSolvable moduleSubgroup)
    (hnormal : acting ≤ normalizer (moduleSubgroup : Set G))
    (hcentral : core ≤ centralizer (moduleSubgroup : Set G))
    (hfixed : moduleSubgroup ⊓ centralizer (acting : Set G) = ⊥)
    (hbound : ⁅moduleSubgroup, acting⁆ ≤ bound) : moduleSubgroup ≤ bound := by
  classical
  have hcoreNative : IsPGroup 2 (core.subgroupOf acting) :=
    htwoCore.of_equiv (subgroupOfEquivOfLe hcore).symm
  have hcoprime : Nat.Coprime (Nat.card (core.subgroupOf acting))
      (core.subgroupOf acting).index := by
    obtain ⟨exponent, hcard⟩ := hcoreNative.exists_card_eq
    rw [hcard]
    exact hodd.coprime_two_left.pow_left exponent
  obtain ⟨complementNative, hcomplement⟩ := exists_right_complement'_of_coprime hcoprime
  let complement := complementNative.map acting.subtype
  have hcomplementLe : complement ≤ acting := map_subtype_le _
  have hcomplementOdd : Odd (Nat.card complement) := by
    rw [card_map_of_injective acting.subtype_injective,
      ← hcomplement.symm.index_eq_card]
    exact hodd
  have hfactor : acting = core ⊔ complement := by
    have hmapped := congrArg (fun subgroup : Subgroup acting =>
      subgroup.map acting.subtype) hcomplement.sup_eq_top
    rw [map_sup, map_subgroupOf_eq_of_le hcore,
      ← MonoidHom.range_eq_map, range_subtype] at hmapped
    exact hmapped.symm
  have hcoprimeModule : Nat.Coprime (Nat.card complement) (Nat.card moduleSubgroup) := by
    obtain ⟨exponent, hcard⟩ := htwoModule.exists_card_eq
    rw [hcard]
    exact hcomplementOdd.coprime_two_right.pow_right exponent
  have hcomplementFixed : moduleSubgroup ⊓ centralizer (complement : Set G) = ⊥ := by
    apply bot_unique
    rw [← hfixed]
    refine le_inf inf_le_left ?_
    apply le_centralizer_iff.mp
    rw [hfactor]
    exact sup_le (hcentral.trans (centralizer_le inf_le_left))
      (le_centralizer_iff.mp inf_le_right)
  have hdecomposition := eq_commutator_sup_centralizer_of_solvable_coprime
    moduleSubgroup complement (hcomplementLe.trans hnormal) hsolvable hcoprimeModule
  rw [hcomplementFixed, sup_bot_eq] at hdecomposition
  rw [hdecomposition]
  exact (commutator_mono le_rfl hcomplementLe).trans hbound

end Subgroup
