module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Evaluation
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word14
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word17
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word20
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word23
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word26
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word29
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.StagesTwoFour.Edges.Tables.Word32

/-!
# The eight cached ambient word actions

The tables include both signs, with `true` denoting the forward action.
They are numerical witnesses on the entire degree-306936 set. Their agreement
with the literal model is the separate proposition `MapsCorrect cachedMaps`;
this module asserts no such comparison. See `Edges/source/generate.py`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges

def cachedMaps : NumericalMaps
  | 0, b => if b then Tables.Word11.forward else Tables.Word11.backward
  | 1, b => if b then Tables.Word14.forward else Tables.Word14.backward
  | 2, b => if b then Tables.Word17.forward else Tables.Word17.backward
  | 3, b => if b then Tables.Word20.forward else Tables.Word20.backward
  | 4, b => if b then Tables.Word23.forward else Tables.Word23.backward
  | 5, b => if b then Tables.Word26.forward else Tables.Word26.backward
  | 6, b => if b then Tables.Word29.forward else Tables.Word29.backward
  | 7, b => if b then Tables.Word32.forward else Tables.Word32.backward

end Sporadic.Fischer.Fi24Prime.Fi23Lift.FirstFourModel.StagesTwoFour.Edges
