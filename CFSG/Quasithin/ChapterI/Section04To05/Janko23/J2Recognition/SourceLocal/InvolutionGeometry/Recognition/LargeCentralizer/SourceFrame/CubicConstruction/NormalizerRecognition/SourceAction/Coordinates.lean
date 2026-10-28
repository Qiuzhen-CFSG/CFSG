module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.RootQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Center
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Coordinates.FactorGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Coordinates.CenterAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Coordinates.Recognition

/-!
# Intrinsic coordinates for the source root group

The two actual extraspecial cores give anisotropic factors in R. Their
coordinate-free action is transitive on the nonidentity elements of E = Z(R),
so conjugation balances the three nonidentity central square fibers. The
multiplication recognition theorem then constructs an isomorphism from R
to the literal UT₃(F₄) carrier, for every returning pair.

The existential theorem supplies the coordinate input to the separate
normalizer-action assembly. This establishes the root-group identification
in 46.14(1); the normalizer image and its splitting remain separate results.
Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and proof of
46.14, printed pp.29–30,251,257–258.
-/

public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Coordinates

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The actual root product of every returning pair is UT₃(F₄). The action
on its center is proved from the source cores, so no extra action or
coordinate hypothesis is required. -/
theorem rootEquiv (P : ReturningPair D) (L : LocalCensus D) :
    Nonempty (P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) :=
  rootEquiv_of_centerTransitive P L (centerTransitive P L)

/-- The source seed and local census supply the exact coordinate witness
required by the normalizer-action assembly. -/
theorem exists_rootEquiv (D : Seed G) (L : LocalCensus D) :
    ∃ P : ReturningPair D, Nonempty (P.R ≃* Matrix.PSL3Four.RootNormalizerModel.Root) := by
  obtain ⟨P⟩ := exists_returningPair D
  exact ⟨P, rootEquiv P L⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Coordinates
