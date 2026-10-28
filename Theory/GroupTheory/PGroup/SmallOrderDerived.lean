module
public import Theory.GroupTheory.PGroup.SmallCentralQuotientDerived

/-! # Cyclic derived subgroups in two-groups of order at most eight -/

public section
open Subgroup
namespace IsPGroup

theorem isCyclic_commutator_of_card_le_eight
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P ≤ 8) :
    IsCyclic (commutator P) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases htrivial : Subsingleton P
  · let := htrivial
    infer_instance
  have : Nontrivial P := not_subsingleton_iff_nontrivial.mp htrivial
  have hcenter : 2 ≤ Nat.card (center P) := by
    have hn : (center P : Subgroup P) ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (center P)).mp (center_nontrivial hP)
    exact (center P).one_lt_card_iff_ne_bot.mpr hn
  have hquot : Nat.card (P ⧸ center P) ≤ 4 := by
    have hm := (center P).card_mul_index
    change Nat.card (center P) * Nat.card (P ⧸ center P) = Nat.card P at hm
    nlinarith
  exact hP.isCyclic_commutator_of_card_center_quotient_le_four hquot

end IsPGroup
