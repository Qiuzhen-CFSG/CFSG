module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.Certificate
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.StageZero.Seeds

/-!
# Stage-zero representatives and the orientation of the remaining certificate

There are 31671 actual word-defined representatives. Their initial value,
base-return separation, and all defining edges have been checked in
`StageZero.Representatives`; `StageZero.Seeds` supplies two further transitions
with the exact factors word5 and word8. The remaining input is a family of full ambient
Schreier identities with factors in the literal stage-one subgroup.

The coset-word checker uses right multiplication. Taking inverses converts its
negative singleton facts into the positive left transitions of `PositiveTable`.
`reduction_of_right_transitions` applies that conversion to the actual consumer.
Neither this conversion nor the defining-tree certificate constructs the
missing transitions; an unconditional `stageZeroTable` is not yet provided.

Source: GLS3 Table 5.3v, ATLAS F24G1-p306936B0, and Schreier rewriting.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo
open Subgroup.CosetWordCertificate

/-- Interface for independently checked right-coset facts. Each fact is an
actual equality in `Perm (Fin 306936)`, with a factor in the literal `stage 1`.
The generator is negative because the eventual left transition is positive. -/
@[expose] def StageZero.RightTransitions : Prop :=
  ∀ (a : Fin 2) (j : Fin 31671), ∃ k : Fin 31671,
    Holds (stage 1) (generators 0) (StageZero.definitions.repr (generators 0))
      ⟨j.val, [(a, false)], k.val⟩

/-- Invert the checked right-coset equalities and use the already certified
initial representative and base-return separation. This is conditional on the
full transition certificate; it asserts no unconditional stabilizer inclusion. -/
def StageZero.tableOfRightTransitions (ht : StageZero.RightTransitions) :
    PositiveTable 0 (Fin 31671) where
  representative := StageZero.representative
  initial := 0
  initial_eq := StageZero.representative_zero
  step a j := by
    obtain ⟨k, h, he⟩ := ht a j
    refine ⟨k, h⁻¹, ?_⟩
    change generators 0 a * StageZero.representative j =
      StageZero.representative k * h.val⁻¹
    have hi := congrArg Inv.inv he
    simpa only [eval_letter, Bool.false_eq_true, ite_false, mul_inv_rev, inv_inv,
      StageZero.representative, StageZero.representativeNat] using hi
  returns_base := StageZero.returns_base

/-- Application to the literal stage-zero stabilizer problem. The right-coset
transition certificate remains an explicit, undischarged premise. -/
theorem StageZero.reduction_of_right_transitions (ht : StageZero.RightTransitions)
    (g : Equiv.Perm (Fin 306936)) (hg : g ∈ stage 0)
    (hfix : g (point 0) = point 0) : g ∈ stage 1 :=
  (StageZero.tableOfRightTransitions ht).reduction g hg hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesZeroTwo
