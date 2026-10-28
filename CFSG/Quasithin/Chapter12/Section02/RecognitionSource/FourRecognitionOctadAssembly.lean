module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionAssembly
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceRecognition

/-!
# Dimension-four assembly with the source Mathieu branch discharged

The source-local normalizer producer and the actual 759-octad comparison
now prove the Mathieu uniqueness alternative directly from its fusion
pattern. This application removes the Mathieu witness premise from the
existing source assembly. The independent matrix comparison, local fusion
classification and linear uniqueness arguments remain explicit inputs to
the dimension-four assembly owner.

Source: Aschbacher–Smith 12.2.27(1), p.807; Aschbacher, *Sporadic Groups*
(1994), 39.1–41.6, pp.213–222.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual octad uniqueness theorem supplies the entire Mathieu branch
without any graph, local-placement or group-recognition callback. -/
theorem four_recognition_of_source_inputs_of_octad_uniqueness {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G)
      (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (linearUnique : IsSimpleGroup G → ∀ (z : G)
      (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.LinearFusion →
        Nonempty (G ≃* BinaryLinear.TransvectionFiveLocal.SL)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_source_inputs h D C hnone compare localTypes
  intro hs z F hcore
  exact ⟨linearUnique hs z F hcore,
    TransvectionFive.mathieu_of_mathieuFusion_source F hs hcore⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
