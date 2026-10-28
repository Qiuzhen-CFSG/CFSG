module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CenterCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.EdgeConfigurations.LocalIncidence.PureFourCentralizer.Transport

/-!
# The intrinsic pure-four centralizer calculation

The center centralizer in the marked root-normalizer model is the actual
Heisenberg cubic extension, with its coordinate action and ambient inclusion.
This discharges `ModelCenterCentralizer` in the existing transport theorem.
Applying that transport gives every pure-four centralizer its model, conditional
only on the separately owned marked normalizer identification.

Source: Aschbacher, *Sporadic Groups* (1994), 46.3, 46.14 and the proof of
47.6(1), printed pp.251, 257–258, 264.
-/

public section
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
open InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame

/-- The independent intrinsic-model premise is now proved without ambient inputs. -/
theorem modelCenterCentralizer : ModelCenterCentralizer :=
  ⟨Matrix.PSL3Four.RootNormalizerModel.CenterCentralizer.equivalence⟩

/-- Pure-four centralizers acquire their actual model from marked normalizer
recognition; the intrinsic centralizer-calculation premise is discharged. -/
theorem models_of_normalizer_calculation {G : Type*} [Group G] [Finite G]
    {D : Seed G} (P : ReturningPair D) (I : NormalizerIdentification P) :
    PureFourCentralizerModels D :=
  models_of_normalizer P I modelCenterCentralizer

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.EdgeConfigurations.PureFourCentralizer
