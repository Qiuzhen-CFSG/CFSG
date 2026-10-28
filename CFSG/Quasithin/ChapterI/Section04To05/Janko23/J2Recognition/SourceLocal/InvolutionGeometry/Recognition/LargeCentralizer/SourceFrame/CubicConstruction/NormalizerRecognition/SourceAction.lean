module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.Action
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.RootQuotient
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Center
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Coordinates
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer

/-!
# Assembly of the source root action

The two extraspecial cores construct actual UT₃(F₄) coordinates on the root
group. The full normalizer-image calculation adjusts those coordinates so
that its conjugation image is exactly the join of the inner automorphisms
and the published diagonal and graph-field actors. The center calculation
discharges self-centralization using the same source core geometry.

The final theorems construct `RootAction` for every returning pair, and hence
the existential witness used by normalizer recognition. They require only
the seed and local census; all coordinate and image premises of the retained
conditional assembly are discharged. Constructing a normalizer complement
is the separate splitting obligation.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and 46.14,
printed pp.29–30, 251 and 257–258.
-/

@[expose] public section

open Subgroup Matrix.PSL3Four

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The unconditional center theorem supplies the remaining field once the
literal coordinates and full conjugation image have been proved. -/
noncomputable def rootAction_of_image (P : ReturningPair D)
    (e : P.R ≃* RootNormalizerModel.Root)
    (himage : (conjugation P e).range =
      (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
        RootNormalizerModel.actor) : RootAction P where
  coordinates := e
  selfCentralizing := selfCentralizing P
  image := himage

/-- Assembly for independent coordinate and action-recognition producers.
The action producer is allowed to adjust the supplied coordinates. -/
theorem exists_rootAction_of_coordinates_and_adjustment
    (hcoordinates : ∃ P : ReturningPair D, Nonempty (P.R ≃* RootNormalizerModel.Root))
    (hadjustment : ∀ (P : ReturningPair D) (e : P.R ≃* RootNormalizerModel.Root),
      ∃ a : MulAut RootNormalizerModel.Root,
        (conjugation P (e.trans a)).range =
          (MulAut.conj : RootNormalizerModel.Root →* MulAut RootNormalizerModel.Root).range ⊔
            RootNormalizerModel.actor) :
    ∃ P : ReturningPair D, Nonempty (RootAction P) := by
  obtain ⟨P, ⟨e⟩⟩ := hcoordinates
  obtain ⟨a, ha⟩ := hadjustment P e
  exact ⟨P, ⟨rootAction_of_image P (e.trans a) ha⟩⟩

/-- Every source returning pair admits root coordinates with the exact full
normalizer action. The core geometry supplies self-centralization, and the
coordinate adjustment supplies the literal image equality. -/
theorem nonempty_rootAction (P : ReturningPair D) (L : LocalCensus D) :
    Nonempty (RootAction P) := by
  obtain ⟨e⟩ := Coordinates.rootEquiv P L
  obtain ⟨a, ha⟩ := Automizer.exists_adjustment P L e
  exact ⟨rootAction_of_image P (e.trans a) ha⟩

/-- The source action input to full normalizer recognition, with both
independently proved coordinate and image obligations discharged. -/
theorem exists_rootAction (D : Seed G) (L : LocalCensus D) :
    ∃ P : ReturningPair D, Nonempty (RootAction P) :=
  exists_rootAction_of_coordinates_and_adjustment
    (Coordinates.exists_rootEquiv D L) (fun P e => Automizer.exists_adjustment P L e)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction
