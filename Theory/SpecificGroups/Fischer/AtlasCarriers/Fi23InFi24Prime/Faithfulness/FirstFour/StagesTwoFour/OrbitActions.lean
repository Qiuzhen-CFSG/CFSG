module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.First
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.OrbitActions.Second

/-!
# Literal inverse actions on the two middle Fischer orbit tables

Shared intermediate computations establish word5 and word8 on 31671 auxiliary
labels. Checked common preimages then establish the inverse actions of word11
and word14 on the 3159 labels. The 630 labels are checked inside that table,
where short products establish the inverse actions of word17 and word20.

Every comparison uses the actual full-degree `aPerm` and `bPerm`. No stabilizer
inclusion, carrier comparison, group order, or faithfulness premise is used.
The separate `OrbitActions.Application` module applies this theorem to the
existing conditional stabilizer reduction without creating an import cycle.
Source: ATLAS F24G1-p306936B0, GLS3 Table 5.3v, retained `source/trees.json`
and `Fi23InFi24Prime/source/faithfulness/nodes.json`.
-/

public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour

/-- Both positive orbit-table transitions are the literal inverse actions. -/
theorem inverseAction : InverseAction := by
  intro i a j
  fin_cases i
  · exact OrbitActions.first_inverse a j
  · exact OrbitActions.second_inverse OrbitActions.first_inverse a j

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour
