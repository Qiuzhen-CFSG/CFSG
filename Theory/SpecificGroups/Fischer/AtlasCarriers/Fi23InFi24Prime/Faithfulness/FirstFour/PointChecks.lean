module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.Model

/-!
# The first four base labels in the checked finite model

These computations evaluate the actual base words in the packed permutations.
`WordBridge.point_eq_actual` transfers them to the original carrier only after
the two full ambient comparisons. They are useful for concrete orbit and
Schreier certificates, but assert no stabilizer inclusions.

Source: ATLAS F24G1-p306936B0, shared `Base.lean`, GLS3 Table 5.3v.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel

theorem point_zero : point 0 = 508 := rfl

theorem point_one : point 1 = 509 := by decide +kernel

theorem point_two : point 2 = 510 := by decide +kernel

theorem point_three : point 3 = 511 := by decide +kernel

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel
