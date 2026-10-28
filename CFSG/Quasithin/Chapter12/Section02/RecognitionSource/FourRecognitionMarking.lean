module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionAssembly
public import Theory.GroupTheory.Recognition.TransvectionFive.Marking

/-!
# The dimension-four recognition assembly with its actual root marking

The original split configuration marks its full translation subgroup as the
column group of the transvection centralizer. Its moving element normalizes
that subgroup, excluding the Held normalizer pattern. This discharges the
matrix-comparison input of the recognition assembly, alongside the already
proved uniqueness implications. The source fusion alternatives of §§39–40
remain explicit here and belong to the same final assembly owner,
`qt-d-12213-four-recognition`.

Source: Aschbacher–Smith 12.2.27(1), p.807; Aschbacher, *Sporadic Groups*
(1994), 39.1(2), 40.5 and 41.6, pp.213,219–222.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- The original seed is the literal column root group, and its normalizer
rules out the Held pattern for this same marking. -/
theorem SplitLinearConfiguration.exists_nonheld_marking
    (C : SplitLinearConfiguration L V 4) (D : ChosenModule T L V)
    (hnone : NoEscape L V) {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    ∃ F : TransvectionFive.MarkedCentralizer z,
      V = F.column ∧ TransvectionFive.PointCoreFusion z ∧ ¬ F.HeldNormalizerPattern := by
  obtain ⟨M⟩ := C.exists_point_marking D hnone hz hz1
  let F := TransvectionFive.markingOfAffine M hz1
  have hV : V = F.column := TransvectionFive.markingOfAffine_column M hz1
  exact ⟨F, hV, C.point_core_fusion D hnone hz hz1,
    C.not_held_normalizer_pattern D hnone hz hz1 F (Or.inr hV)⟩

/-- The actual 12.2.27(1) consumer with the marking and both uniqueness
branches discharged. The remaining source fusion theorem is owned here. -/
theorem four_recognition_of_fusion {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  four_recognition_of_marking_and_fusion h D C hnone
    TransvectionFive.exists_marking_of_affine localTypes

/-- Preserve the dimension in the recognition interface after the actual
marking construction. The only remaining input is the source fusion theorem. -/
theorem recognized_four_of_fusion {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern) :
    RecognizedGroup G 4 :=
  recognized_four_of_classical_or_mathieu (four_recognition_of_fusion h D C hnone localTypes)

/-- The literal block of the original configuration supplies the 12.2.13
branch once the remaining source fusion theorem is proved. -/
theorem alternatives_four_of_fusion {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern) :
    Alternatives12213 T L V :=
  alternatives_four_of_classical_or_mathieu C (four_recognition_of_fusion h D C hnone localTypes)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
