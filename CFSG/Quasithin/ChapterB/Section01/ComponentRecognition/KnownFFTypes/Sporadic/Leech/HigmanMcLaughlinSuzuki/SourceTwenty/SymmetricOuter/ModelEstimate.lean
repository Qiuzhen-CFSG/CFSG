module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.SymmetricOuter.ModelEstimate.Reduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.SymmetricOuter.ModelEstimate.DualComparison

/-!
# The rank-three estimate on the induced S8 eight-space

An odd actor has a common fixed space of dimension at most four. For an
actor contained in A8, the proved marked outer-dual comparison identifies
the model with the natural four-space and its dual. The intrinsic faithful
rank bound then gives total fixed codimension at least four. This includes
regular E8 actors, without selecting a special involution cycle type.
The resulting unconditional model estimate supplies the induced-eight
input to the HS filtration calculation.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, pp.16--17; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Symmetric

/-- Both branches give exactly the model estimate consumed by the HS
filtration, with the remaining equivariant comparison explicit. -/
theorem inducedRankThreeBound_of_outerDualComparison
    (hdual : HasOuterDualComparison) : InducedRankThreeBound := by
  intro B _hB hr
  by_cases hBA : B ≤ alternatingGroup (Fin 8)
  · exact induced_fixedCodim_ge_four_of_outerDualComparison hdual B hBA hr
  · exact induced_fixedCodim_ge_four_of_not_le_alternating B hBA

/-- Every elementary subgroup of rank at least three has fixed codimension
at least four on the actual induced eight-space, including regular E8 actors. -/
theorem inducedRankThreeBound : InducedRankThreeBound :=
  inducedRankThreeBound_of_outerDualComparison outerDualComparison

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Symmetric
