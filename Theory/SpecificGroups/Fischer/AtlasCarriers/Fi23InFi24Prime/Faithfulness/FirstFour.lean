module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Base
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.StabilizerWords
public import Theory.GroupAction.GeneratorStabilizerReduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PointChecks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.WordBridge

/-!
# Assembly of the first four Fi₂₃ lift stabilizer reductions

The finite model has kernel-checked permutations and precisely the same
straight-line words and base words as the original carrier. The theorem below
transports its four stabilizer inclusions through the injective ambient
inclusion, provided the two full permutation comparisons have been proved.

The unconditional `wordStage_first_four_reductions` remains to be assembled:
its missing inputs are the full candidate-permutation comparisons and the
four finite-model stabilizer certificates. Neither the checked inverse laws
nor this conditional transport asserts the missing stabilizer inclusions.
Source: GLS3 Table 5.3v and ATLAS F24G1-p306936B0.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift

/-- Model certificates transfer to the literal first four stabilizers only
after both full ambient permutation comparisons are supplied. -/
theorem wordStage_first_four_reductions_of_model
    (ha : candidateA.val = FirstFourModel.aPerm)
    (hb : candidateB.val = FirstFourModel.bPerm)
    (step : ∀ i : Fin 4, ∀ g : Equiv.Perm (Fin 306936),
      g ∈ FirstFourModel.stage i.castSucc →
      g (FirstFourModel.point i) = FirstFourModel.point i →
      g ∈ FirstFourModel.stage i.succ) :
    ∀ i : Fin 4, ∀ g : Carrier, g ∈ wordStage (i.castAdd 4).castSucc →
      g.val (basePoint (i.castAdd 4)) = basePoint (i.castAdd 4) →
      g ∈ wordStage (i.castAdd 4).succ :=
  FirstFourModel.actual_reductions_of_compared_permutations
    FirstFourModel.aPerm FirstFourModel.bPerm ha hb step

end Sporadic.Fischer.Fi24Prime.Fi23Lift
