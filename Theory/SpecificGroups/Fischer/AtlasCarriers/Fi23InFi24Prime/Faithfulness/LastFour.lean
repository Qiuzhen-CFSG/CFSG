module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Base
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.StabilizerWords
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.LastFour.Setup
public import Theory.GroupAction.GeneratorStabilizerReduction

/-!
# Assembly of the final four Fi₂₃ lift stabilizer reductions

The concrete tables supply representatives, factor words, inverse transitions,
and separation of the marked points. Generator-action checks and the actual
transition identities imply that the following subgroup fixes each base point.
Schreier decomposition then gives the required point-stabilizer inclusions.

The finite identities remain explicit in this conditional theorem. The
unconditional `wordStage_last_four_reductions` must discharge them before this
module supplies the final faithfulness assembly. No first-four inclusion, group
order, Fi₂₃ recognition, or faithfulness premise is used. Source: GLS3 Table 5.3v
and ATLAS F24G1-p306936B0; see `LastFour/source/README.md`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour

/-- The exact finite equalities construct all fields of the Schreier certificate.
The next-stage fixed-point property follows from the witnessed singleton factors. -/
def reduction (steps : StepIdentities) (bases : BaseIdentities) (points : PointIdentities)
    (i : Fin 4) :
    Subgroup.GeneratorStabilizerReduction (generator i.castSucc)
      (wordStage (i.natAdd 4).succ) (basePoint (i.natAdd 4)) (Fin (orbitSize i)) := by
  apply Subgroup.GeneratorStabilizerReduction.ofPermutations
    (generator i.castSucc) (wordStage (i.natAdd 4).succ) (basePoint (i.natAdd 4))
    (representative i) (initial i) (representative_initial i) (transition i)
    (fun a j => ⟨factor i a j, factor_mem i a j⟩) (steps i)
  · have hs : wordStage (i.natAdd 4).succ ≤
        MulAction.stabilizer Carrier (basePoint (i.natAdd 4)) := by
      change wordStage (i.succ.natAdd 4) ≤ _
      rw [← generated i.succ]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨a, rfl⟩
      exact generator_next_fixes steps bases points i a
    intro k
    exact hs k.property
  · intro j hj
    change (representative i j).val (basePoint (i.natAdd 4)) = basePoint (i.natAdd 4) at hj
    rw [representative_apply bases points, bases i] at hj
    rw [orbitPoint_returns i j hj, representative_initial]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.LastFour

namespace Sporadic.Fischer.Fi24Prime.Fi23Lift

/-- Concrete certificate assembly for the last four literal word stages.
The global permutation identities and the numerical point checks remain explicit. -/
theorem wordStage_last_four_reductions_of_certificates
    (steps : LastFour.StepIdentities) (bases : LastFour.BaseIdentities)
    (points : LastFour.PointIdentities) :
    ∀ i : Fin 4, ∀ g : Carrier, g ∈ wordStage (i.natAdd 4).castSucc →
      g.val (basePoint (i.natAdd 4)) = basePoint (i.natAdd 4) →
      g ∈ wordStage (i.natAdd 4).succ := by
  intro i g hg hfix
  apply (LastFour.reduction steps bases points i).mem_next
  · rwa [LastFour.generated i.castSucc]
  · exact hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift
