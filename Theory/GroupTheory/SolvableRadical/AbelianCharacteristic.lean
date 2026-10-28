module

public import Theory.GroupTheory.SolvableRadical
public import Theory.GroupTheory.SolvableNormalAbelian

/-!
# Detecting the solvable radical by characteristic abelian subgroups

In a finite group, a nontrivial solvable radical has a last nontrivial
derived subgroup. This subgroup is abelian and characteristic in the radical,
and hence characteristic in the whole group. Conversely, every characteristic
abelian subgroup lies in the solvable radical.

This is the elementary reduction to abelian normal subgroups used in local
maximal-subgroup analysis. It does not identify any finite simple group.
Source: the derived-series argument and the definition of the solvable radical.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- Nontriviality of the solvable radical supplies an actual characteristic
abelian subgroup of the original group. -/
theorem exists_abelian_characteristic_of_solvableRadical_ne_bot
    (hR : solvableRadical G ≠ ⊥) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ A ≠ ⊥ := by
  let R := solvableRadical G
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hR
  obtain ⟨A, hAchar, hAcomm, hAne⟩ :=
    Group.exists_nontrivial_abelian_characteristic R
  let := hAchar
  let := hAcomm
  refine ⟨A.map R.subtype, inferInstance, inferInstance, ?_⟩
  exact fun h => hAne ((map_eq_bot_iff_of_injective A R.subtype_injective).mp h)

/-- For finite groups, absence of characteristic abelian subgroups is
equivalent to triviality of the solvable radical. -/
theorem solvableRadical_eq_bot_iff_abelian_characteristic_eq_bot :
    solvableRadical G = ⊥ ↔
      ∀ A : Subgroup G, A.Characteristic → IsMulCommutative A → A = ⊥ := by
  constructor
  · intro hR A hAchar hAcomm
    let := hAchar
    let := hAcomm
    exact le_bot_iff.mp (hR ▸ le_solvableRadical A inferInstance
      (Group.isSolvable_of_comm (fun a b => mul_comm' a b)))
  · intro h
    by_contra hR
    obtain ⟨A, hAchar, hAcomm, hAne⟩ :=
      exists_abelian_characteristic_of_solvableRadical_ne_bot hR
    exact hAne (h A hAchar hAcomm)

end Subgroup
