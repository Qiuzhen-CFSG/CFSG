module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Deductions
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Shape
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.Faithfulness.Exact.Cover.Construction

/-!
# The proved centralizer cover for the HS presentation

The 331,989 checked deductions yield all 23,100 signed transitions on 5,775
representatives. This is a cover by right cosets of the centralizer of the
first abstract generator. No finiteness or permutation faithfulness enters.
Source: ATLAS HSG1-P1.M; reproduction details are in `Cover/source/README.md`.
-/

namespace Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover

/-- The source centralizer-index upper bound, as an explicit finite cover. -/
@[expose] public def cover : Subgroup.GeneratorCosetCover centralizer generator (Fin 5775) :=
  cover_of_checked all_hold all_shapes

end Sporadic.LeechRelated.HS.AtlasPresentation.Exact.Cover
