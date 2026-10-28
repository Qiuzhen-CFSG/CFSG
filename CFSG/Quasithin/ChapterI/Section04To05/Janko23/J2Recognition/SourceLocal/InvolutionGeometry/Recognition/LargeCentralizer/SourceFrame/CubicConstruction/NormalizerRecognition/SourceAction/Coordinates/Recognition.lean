module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Coordinates.FactorGeometry

/-!
# Recognizing the multiplication of the source root group

The source factor geometry supplies both anisotropic planes and their
centralizer condition. The explicit center-action hypothesis balances the
literal square fibers. The generic recognition theorem constructs marked
binary normal forms, restricts their multiplication to six cross matrices,
and identifies each with the literal UT₃(F₄) carrier.

The source application takes only the returning pair, local census and
explicit center transitivity. The parent source assembly must discharge
that independent action hypothesis. This proves the root-group recognition
step in 46.14(1), without asserting its other normalizer and fusion clauses.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and proof of
46.14, printed pp.29–30,251,257–258.
-/

public section
open Theory.GroupTheory.AnisotropicRecognition

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Coordinates

/-- The actual source root factors satisfy the checked six-case criterion
whenever marked binary normal forms have been constructed. -/
theorem crossCases_of_coordinates {G : Type*} [Group G] [Finite G]
    {D : Seed G} (P : ReturningPair D) (L : LocalCensus D)
    (h : CenterTransitive P) (C : MarkedCoordinates (rootFactors P L)) :
    SixCases C.matrix :=
  sixCases_of_coordinates (rootFactors P L) C (squareFibers_balanced P h)

/-- The literal source root group is UT₃(F₄), assuming only the independent
source action on its nonidentity central elements. No coordinate witness
or model action is an additional premise. -/
theorem rootEquiv_of_centerTransitive {G : Type*} [Group G] [Finite G]
    {D : Seed G} (P : ReturningPair D) (L : LocalCensus D)
    (h : CenterTransitive P) :
    Nonempty (P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :=
  rootEquiv_of_balanced (rootFactors P L) (squareFibers_balanced P h)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Coordinates
