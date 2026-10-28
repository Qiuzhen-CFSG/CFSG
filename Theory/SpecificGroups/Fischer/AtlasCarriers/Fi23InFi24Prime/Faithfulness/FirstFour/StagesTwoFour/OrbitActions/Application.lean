module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour

/-!
# Application of the checked middle orbit actions

The literal action comparisons discharge `InverseAction` in the existing
stabilizer reduction. Only the nontree Schreier memberships remain explicit;
the parent assembly owns that independent input.
Source: ATLAS F24G1-p306936B0 and GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
open StagesTwoFour

/-- The checked action comparisons leave only nontree memberships to discharge. -/
theorem second_two_reductions_of_nonTreeEdges (he : NonTreeEdges) :
    ∀ i : Fin 2, ∀ g : Equiv.Perm (Fin 306936),
      g ∈ stage (i.natAdd 2).castSucc →
      g (point (i.natAdd 2)) = point (i.natAdd 2) →
      g ∈ stage (i.natAdd 2).succ :=
  second_two_reductions_of_certificates inverseAction he

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
