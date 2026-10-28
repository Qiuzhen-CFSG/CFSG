module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.Reduction
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy

/-!
# Applying the root-automorphism classification to the source normalizer

The model classification applies to the literal image of normalizer conjugation,
retaining the supplied root isomorphism and its actual change of coordinates.
All concrete model obligations are discharged. The separate source construction
still supplies `SourceInvariants`; the final application has only that premise
in addition to the supplied root isomorphism.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.3 and 46.14,
printed pp.29–30, 251, and 257–258.
-/

@[expose] public section

open Subgroup Matrix.PSL3Four
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
open RootNormalizerModel.AutomizerConjugacy

variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

/-- The actual adjusted-image equality, with the remaining model calculations explicit. -/
theorem exists_adjustment_of_model_structure
    (e : P.R ≃* RootNormalizerModel.Root) (h : SourceInvariants P)
    (hsyl : ∃ T : Sylow 3 (MulAut RootNormalizerModel.Root),
      (T : Subgroup (MulAut RootNormalizerModel.Root)) = torus)
    (hnormal : normalizer (innerTorus : Set (MulAut RootNormalizerModel.Root)) ≤
      RootNormalizerModel.AutomizerConjugacy.inner ⊔ semilinear)
    (recognize : ∀ K : Subgroup (MulAut RootNormalizerModel.Root),
      RootNormalizerModel.AutomizerInvariants K → torus ≤ K →
      K ≤ RootNormalizerModel.AutomizerConjugacy.inner ⊔ semilinear →
      K = RootNormalizerModel.AutomizerConjugacy.inner ⊔ RootNormalizerModel.actor) :
    ∃ a : MulAut RootNormalizerModel.Root,
      (conjugation P (e.trans a)).range =
        (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
          RootNormalizerModel.actor := by
  exact exists_adjustment_of_source_invariants P e h
    (exists_adjustment_of_semilinear_classification hsyl hnormal recognize)

/-- The source invariants suffice for the original literal adjusted-image
equality, by the unconditional concrete root-automorphism classification. -/
theorem exists_adjustment_of_source
    (e : P.R ≃* RootNormalizerModel.Root) (h : SourceInvariants P) :
    ∃ a : MulAut RootNormalizerModel.Root,
      (conjugation P (e.trans a)).range =
        (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
          RootNormalizerModel.actor :=
  exists_adjustment_of_source_invariants P e h
    RootNormalizerModel.AutomizerConjugacy.exists_adjustment_of_invariants

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
