module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.Data
public import Mathlib.GroupTheory.Index

/-!
# Removing the odd half of the colored graph group

An odd symmetry makes the even subgroup proper. Its index is therefore at least
two, so a bound of 2048 on the entire colored graph group gives a bound of 1024
on its even subgroup. The graph bound and the odd symmetry are explicit inputs;
their finite certificates do not require any identification with He:2.

Source context: the concrete graph route to GLS3 Table 5.3p, with candidate data
in the sibling Data module. The argument is the ordinary subgroup-index formula.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
open Subgroup

/-- An odd colored graph symmetry halves the cardinal upper bound. -/
public theorem even_card_le_of_odd
    (hcard : Nat.card coloredGraphGroup ≤ 2048)
    (σ : Equiv.Perm (Fin 2058)) (hσ : σ ∈ coloredGraphGroup)
    (hodd : Equiv.Perm.sign σ ≠ 1) : Nat.card evenColoredGraphGroup ≤ 1024 := by
  let E := evenColoredGraphGroup.subgroupOf coloredGraphGroup
  have hproper : E ≠ ⊤ := by
    intro he
    have hm : (⟨σ, hσ⟩ : coloredGraphGroup) ∈ E := he ▸ Subgroup.mem_top _
    exact hodd hm.2
  have hi : 2 ≤ E.index := E.one_lt_index_of_ne_top hproper
  have he : Nat.card E = Nat.card evenColoredGraphGroup :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show evenColoredGraphGroup ≤ coloredGraphGroup from inf_le_left)).toEquiv
  have hb : Nat.card evenColoredGraphGroup * 2 ≤ Nat.card coloredGraphGroup := by
    rw [← he, ← E.card_mul_index]
    exact Nat.mul_le_mul_left _ hi
  omega

end Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
