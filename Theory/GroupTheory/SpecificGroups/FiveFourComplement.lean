module

public import Theory.GroupTheory.SpecificGroups.FiveFour
public import Theory.GroupTheory.C5C4NormalTwoSubgroup
public import Mathlib.GroupTheory.Complement

/-!
# Embedded five-by-four groups and normal two-subgroups

An embedded faithful `C₅ : C₄` intersects every normal two-subgroup
trivially: the inverse image of the intersection is a normal two-subgroup
of the Frobenius group. If the orders multiply to the ambient order,
this gives an actual complement. No splitting assertion is extracted
from an abstract quotient isomorphism.
-/

namespace FiveFour
open Subgroup

/-- An embedded five-by-four group avoids every normal two-subgroup. -/
public theorem disjoint_range_of_normal_two_subgroup
    {H : Type*} [_root_.Group H] (j : Group →* H)
    (hj : Function.Injective j) (N : Subgroup H) [N.Normal]
    (hN : IsPGroup 2 N) : Disjoint j.range N := by
  let B : Subgroup Group := (SemidirectProduct.inl : Cyclic 5 →* Group).range
  have hB : Nat.card B = 5 := by
    rw [← Nat.card_congr
      (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    change Nat.card (ZMod 5) = 5
    simp
  have hbot : N.comap j = ⊥ :=
    SemidirectProduct.two_subgroup_eq_bot_of_five_normalizes
      action action_injective B (N.comap j) hB (hN.comap_of_injective j hj)
      (by rw [normalizer_eq_top]; exact le_top)
  apply disjoint_iff.mpr
  apply bot_unique
  rintro x ⟨⟨g, rfl⟩, hg⟩
  have hg1 : g = 1 := mem_bot.mp (hbot ▸ show g ∈ N.comap j from hg)
  simp [hg1]

/-- Cardinality finishes complementarity only after an actual embedding
and a trivial intersection have been established. -/
public theorem isComplement_range_of_normal_two_subgroup
    {H : Type*} [_root_.Group H] [Finite H] (j : Group →* H)
    (hj : Function.Injective j) (N : Subgroup H) [N.Normal]
    (hN : IsPGroup 2 N) (hcard : 20 * Nat.card N = Nat.card H) :
    j.range.IsComplement' N := by
  apply isComplement'_of_card_mul_and_disjoint
  · rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, card]
    exact hcard
  · exact disjoint_range_of_normal_two_subgroup j hj N hN

end FiveFour
