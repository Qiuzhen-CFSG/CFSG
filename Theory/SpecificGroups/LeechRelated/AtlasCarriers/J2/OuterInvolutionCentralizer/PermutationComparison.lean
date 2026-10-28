module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.UpperBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.LowerBound

/-!
# The representative outer fixed subgroup and its faithful fourteen-point model

The checked normal forms bound the entire fixed subgroup by 336. Two explicit
fixed elements lift the model generators, whose words give 336 distinct images.
The restriction action is therefore faithful and its range is exactly the model.
This gives an isomorphism of whole groups, including surjectivity.

The independent identification of this small model with PGL₂(7) remains
separate; the present equivalence does not assert that source identification.
Sources: GLS3 Table 5.3g, class 2C; Aschbacher--Smith 16.1.5(8), p.1172.
-/

public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
open ExceptionalParabolics

private theorem range_card_le : Nat.card action.range ≤ Nat.card involutionAut.fixedSubgroup :=
  Nat.card_le_card_of_surjective action.rangeRestrict action.rangeRestrict_surjective

private theorem model_card_le_range : Nat.card model ≤ Nat.card action.range :=
  Nat.card_le_card_of_injective (Subgroup.inclusion model_le_range)
    (Subgroup.inclusion_injective model_le_range)

/-- The order is counted for the whole fixed subgroup. -/
theorem card_fixed : Nat.card involutionAut.fixedSubgroup = 336 :=
  le_antisymm card_fixed_le (card_model_ge.trans (model_card_le_range.trans range_card_le))

theorem card_model : Nat.card model = 336 :=
  le_antisymm (model_card_le_range.trans (range_card_le.trans card_fixed_le)) card_model_ge

/-- The explicit model exhausts the image of the entire fixed subgroup. -/
theorem action_range : action.range = model := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge model_le_range
  rw [card_model]
  exact range_card_le.trans card_fixed_le

/-- Cardinality saturation proves faithfulness of the literal restriction action. -/
theorem action_injective : Function.Injective action := by
  apply MonoidHom.rangeRestrict_injective_iff.mp
  apply ((Nat.bijective_iff_surjective_and_card action.rangeRestrict).mpr
    ⟨action.rangeRestrict_surjective, ?_⟩).1
  rw [action_range, card_model, card_fixed]

/-- A bijection and multiplication equivalence for the entire representative fixed group. -/
noncomputable def fixedEquivModel : involutionAut.fixedSubgroup ≃* model :=
  (MonoidHom.ofInjective action_injective).trans (MulEquiv.subgroupCongr action_range)

/-- The equivalence retains the actual restriction of the original permutation. -/
theorem fixedEquivModel_apply (g : involutionAut.fixedSubgroup) :
    (fixedEquivModel g : Equiv.Perm (Fin 14)) = action g := by
  unfold fixedEquivModel
  rfl

end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
