module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.RootReduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.PureFourCentralizer.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.PureFourCentralizer.ModelCalculation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.LocalCensus
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition

/-!
# Pure four-group centralizers in the source group

Every pure z-class four-group is conjugate to the marked E of a returning
pair. Its full centralizer lies in the marked root normalizer. An actual
normalizer identification restricts, with the ambient inclusion retained,
to the center centralizer in the explicit normalizer model.

The earlier-source local census constructs the marked normalizer identification,
and the intrinsic model calculation identifies its center centralizer with the
Heisenberg cubic extension. The marked equivalence below retains the literal
ambient inclusion; conjugacy then proves `PureFourCentralizerModels` from the
seed alone. No simplicity assumption or additional fusion premise is needed.

The application to the inner triple of 47.6(1) discharges its entire centralizer
premise. Only the independent finite-model cubic geometry remains explicit.

Source: Aschbacher, *Sporadic Groups* (1994), 46.1–46.3, 46.14 and
47.6(1), printed pp.251,257–258,264.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer

open InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

variable {G : Type*} [Group G] [Finite G]

/-- The full centralizer of the marked pure four-group has Heisenberg coordinates
whose ambient inclusion is exactly the restriction of the normalizer coordinates.
Both the source recognition and the intrinsic action calculation are discharged. -/
theorem exists_marked_equivalence {D : Seed G} (P : ReturningPair D) :
    ∃ (I : NormalizerIdentification P)
      (e : centralizer (P.E : Set G) ≃* HeisenbergFour.Model),
      ∀ c : centralizer (P.E : Set G),
        Matrix.PSL3Four.RootNormalizerModel.CenterCentralizer.inclusion (e c) =
          I.equiv ⟨(c : G), centralizer_le_normalizer P c.property⟩ := by
  obtain ⟨I⟩ := NormalizerRecognition.nonempty_identification P (localCensus D)
  refine ⟨I, (centralizerCoordinates P I).trans
    Matrix.PSL3Four.RootNormalizerModel.CenterCentralizer.equivalence, ?_⟩
  intro c
  exact (Matrix.PSL3Four.RootNormalizerModel.CenterCentralizer.inclusion_equivalence
    (centralizerCoordinates P I c)).trans (centralizerCoordinates_coe P I c)

/-- Every pure z-class four-group has the actual full-centralizer model used in
47.6(1). The local census, normalizer identification and model calculation are all
proved from the original seed; no extra recognition premise remains. -/
theorem models (D : Seed G) : PureFourCentralizerModels D := by
  obtain ⟨P, ⟨I⟩⟩ := NormalizerRecognition.exists_identification D (localCensus D)
  exact models_of_normalizer_calculation P I

/-- Application to the literal inner triple, including every X-translate.
This supplies the centralizer premise of `inner_sl2Join_of_root_geometry`;
the independently owned finite-model cubic geometry remains explicit. -/
theorem inner_sl2Join (hgeometry : RootModelCubicGeometry) (D : Seed G)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hF : Nonempty (fixer D Y ≃* alternatingGroup (Fin 5)))
    (hclass : ∀ t ∈ fixer D Y, orderOf t = 2 → IsConj D.z t)
    (g : localCentralizer D) (hg : (g : G) ∉ actor D Y)
    (eI : intersection D Y g ≃* alternatingGroup (Fin 4)) (x : D.X) :
    sl2Join D Y ((x : G) • ((g : G) • Y)) :=
  inner_sl2Join_of_root_geometry hgeometry D (models D) Y hY hF hclass g hg eI x

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
