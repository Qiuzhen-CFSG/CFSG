module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.RootQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Center
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.SourceStructure
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.ModelApplication

/-!
# Recognizing the full source automorphism image

For any supplied coordinates on the actual root product R, a change of those
coordinates identifies the full normalizer's conjugation image with the join
of the inner automorphisms and the published diagonal and graph-field actors.

The source core geometry supplies the normalizer order, the full action on
the intrinsic center, and a central cubic coset modulo R. The reduction
transports these facts to the literal root-automorphism image. The concrete
subgroup classification then gives the adjustment and full image equality,
including both containment and realization. All invariant and classification
premises are discharged here; root coordinates remain the explicit input.

This proves the action-recognition step, independently of constructing a
normalizer complement. It does not assert the image equality for arbitrary
unadjusted coordinates.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and 46.14,
printed pp.29–30, 251 and 257–258.
-/

@[expose] public section

open Subgroup Matrix.PSL3Four

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- After changing any supplied root coordinates, the literal full normalizer
conjugation image is exactly the inner–actor join. The source census discharges
all the source invariants required by the concrete automorphism calculation. -/
theorem exists_adjustment (P : ReturningPair D) (L : LocalCensus D)
    (e : P.R ≃* RootNormalizerModel.Root) :
    ∃ a : MulAut RootNormalizerModel.Root,
      (conjugation P (e.trans a)).range =
        (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
          RootNormalizerModel.actor :=
  exists_adjustment_of_source P e (sourceInvariants P L)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
