module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour

/-!
# Application of full ambient factor certificates

Correct cached actions and full-degree arithmetic checks supply the nontree
memberships needed by the existing stabilizer reduction. The inverse action
on the coset labels remains the independent hypothesis owned by OrbitActions.
No conditional input here is claimed as a proved source theorem.
Source: GLS3 Table 5.3v and ATLAS F24G1-p306936B0.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
open StagesTwoFour StagesTwoFour.Edges

/-- The exact consumer, with all outstanding certificate obligations explicit. -/
theorem second_two_reductions_of_ambient_checks
    (hm : MapsCorrect cachedMaps)
    (h₂ : StageChecks cachedMaps 0) (h₃ : StageChecks cachedMaps 1)
    (ha : InverseAction) :
    ∀ i : Fin 2, ∀ g : Equiv.Perm (Fin 306936),
      g ∈ stage (i.natAdd 2).castSucc →
      g (point (i.natAdd 2)) = point (i.natAdd 2) →
      g ∈ stage (i.natAdd 2).succ :=
  second_two_reductions_of_certificates ha
    (nonTreeEdges_of_checks cachedMaps hm h₂ h₃)

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
