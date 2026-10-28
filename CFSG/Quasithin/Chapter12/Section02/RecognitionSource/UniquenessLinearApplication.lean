module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionAssembly
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearRecognition
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceNativeSimilarity
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceGenerationReduction
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondCentralizer
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSecondLocal
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinear

/-!
# Applying the concrete linear cycle base to the four-dimensional branch

The linear uniqueness callback in `four_recognition_of_source_inputs` is
replaced by construction of the literal source coset geometry and compatible
local comparisons. The binary matrix target, its simplicity and its cycle base
are all supplied by the proved model. The earlier marking and local-type inputs
and the separate Mathieu recognition remain explicit, so this does not finish
12.2.27. Their source assembly owners retain their discharge.
The final theorem discharges the linear source comparison, including relative
normality in the literal quotient, marked four-group transport, both
second-centralizer fixed-coset arguments and ambient generation.

Source: Aschbacher–Smith, 12.2.27(1), p.807; Aschbacher, *Sporadic Groups*
(1994), §§40–41, pp.217–222.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Actual dimension-four consumer of the proved linear model and cycle base.
The remaining linear premise is the source normalizer/comparison theorem. -/
theorem four_recognition_of_linear_graph_comparisons {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (linearComparison : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.LinearFusion →
        Nonempty (TransvectionFive.UniquenessLinear.SourceComparison F))
    (mathieu : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.MathieuFusion →
        Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_source_inputs h D C hnone compare localTypes
  intro hs z F hf
  refine ⟨?_, mathieu hs z F hf⟩
  intro hlinear
  obtain ⟨J⟩ := linearComparison hs z F hf hlinear
  exact J.nonempty_equiv

/-- The linear local comparison is now constructed from the original fusion
hypothesis. The sole remaining linear source input is ambient generation by
the literal row and three-space normalizers in 41.1. -/
theorem four_recognition_of_linear_normalizer_generation {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (linearGeneration : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.LinearFusion →
        TransvectionFive.UniquenessLinear.rowNormalizer F ⊔
          TransvectionFive.UniquenessLinear.sourceThreeSpaceNormalizer F = ⊤)
    (mathieu : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.MathieuFusion →
        Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_linear_graph_comparisons h D C hnone compare localTypes
    (mathieu := mathieu)
  intro hs z F hf hl
  exact TransvectionFive.UniquenessLinear.nonempty_sourceComparison_of_generation F hl
    (linearGeneration hs z F hf hl)

/-- The linear branch now needs only the remaining second-involution
centralizer containment. Both involution classes, their fusion, the fixed-coset
generation argument and the literal graph comparison are supplied by the source
proofs. The source centralizer premise and Mathieu recognition remain explicit. -/
theorem four_recognition_of_linear_second_centralizer {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (linearCentralizer : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.LinearFusion →
        Subgroup.centralizer ({TransvectionFive.UniquenessLinear.planeSecondPoint F} : Set G) ≤
          TransvectionFive.UniquenessLinear.normalizerSpan F)
    (mathieu : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.MathieuFusion →
        Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_linear_graph_comparisons h D C hnone compare localTypes
    (mathieu := mathieu)
  intro hs z F hf hl
  exact TransvectionFive.UniquenessLinear.nonempty_sourceComparison_of_second_centralizer F hl
    (linearCentralizer hs z F hf hl)

/-- The remaining linear input consists of the marked four-group transport and
relative normality in the actual centralizer quotient. Point lifts, separation
of both selected classes, both fixed-coset arguments, ambient generation and
the literal source comparison are supplied by the checked source development.
The local data and the separate Mathieu recognition still require producers. -/
theorem four_recognition_of_linear_second_local_data {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (linearLocalData : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.LinearFusion →
        Nonempty (TransvectionFive.UniquenessLinear.SecondCentralizerLocalData F))
    (mathieu : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.MathieuFusion →
        Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_linear_graph_comparisons h D C hnone compare localTypes
    (mathieu := mathieu)
  intro hs z F hf hl
  obtain ⟨E⟩ := linearLocalData hs z F hf hl
  exact TransvectionFive.UniquenessLinear.nonempty_sourceComparison_of_second_local_data F hl E

/-- The original linear branch now supplies its source comparison without a
centralizer, local-data or generation callback. The independent earlier source
inputs and the separate Mathieu recognition remain with their assembly owners. -/
theorem four_recognition_of_linear_source {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (mathieu : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.MathieuFusion →
        Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_source_inputs h D C hnone compare localTypes
  intro hs z F hcore
  exact ⟨TransvectionFive.linear_of_linearFusion F hs hcore, mathieu hs z F hcore⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
