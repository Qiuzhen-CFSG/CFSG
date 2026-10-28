module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.PointChecks
public import Theory.GroupAction.GeneratorStabilizerReduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesZeroTwo.Certificate

/-!
# The first two model stabilizer reductions: certificate assembly

The proposed next subgroups really fix the word-defined points 508 and 509.
The positive-table criterion discharges inverse transitions using finiteness
of the ambient symmetric group, without computing any order. Its remaining
inputs are full-degree Schreier equalities and base-return separation.

The unconditional `first_two_reductions` still requires both positive tables.
This module keeps that assembly boundary explicit; fixed-point computations
alone do not establish either stabilizer inclusion.

Source: ATLAS F24G1-p306936B0 and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel

/-- Assemble the first two inclusions once their actual positive Schreier tables
have been certified. This theorem does not supply those two tables. -/
theorem first_two_reductions_of_positive_tables {I : Fin 2 → Type*}
    (C : ∀ i, StagesZeroTwo.PositiveTable i (I i)) :
    ∀ i : Fin 2, ∀ g : Equiv.Perm (Fin 306936),
      g ∈ stage (i.castAdd 2).castSucc →
      g (point (i.castAdd 2)) = point (i.castAdd 2) →
      g ∈ stage (i.castAdd 2).succ := by
  intro i g hg hfix
  exact (C i).reduction g hg hfix

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
