module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FourRecognitionPreparation
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu
public import Theory.GroupTheory.Recognition.TransvectionFive.Uniqueness

/-!
# Assembly boundary for the dimension-four branch of 12.2.27

The three independent prerequisites are the marked matrix comparison, the
local fusion classification in Aschbacher §§39--40, and the uniqueness
argument of §41 for each surviving fusion pattern. The original V and z
are retained throughout, so the Held pattern is excluded by the source
normalizer argument, not by an assumed no-Held hypothesis.

The source uniqueness argument is now supplied by the proved linear and
native-octad Mathieu branches. `four_recognition_of_marking_and_fusion`
discharges the uniqueness premise of the original assembly; the marked
matrix comparison and local fusion alternatives remain with the
dimension-four assembly owner `qt-d-12213-four-recognition`. The older
conditional assembly APIs are preserved. The section owner owns its umbrella.
Source: Aschbacher--Smith 12.2.27(1), p.807; Aschbacher, *Sporadic Groups*
(1994), 39.1--41.6, pp.213--222.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Conditional source assembly. The uniqueness premise requires actual
ambient isomorphisms from the measured local fusion alternatives. -/
theorem four_recognition_of_source_inputs {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern)
    (unique : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        (F.LinearFusion → Nonempty (G ≃* BinaryLinear.TransvectionFiveLocal.SL)) ∧
        (F.MathieuFusion → Nonempty (G ≃* Sporadic.Mathieu.M24))) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp D.ne_bot
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  obtain ⟨M⟩ := C.exists_point_marking D hnone z.property hz1
  obtain ⟨F, hV⟩ := compare z hz1 M
  have hfusion := C.point_core_fusion D hnone z.property hz1
  have htypes := localTypes h.simpleQTKE.simple z F hfusion
  have hu := unique h.simpleQTKE.simple z F hfusion
  rcases htypes with hlinear | hmathieu | hheld
  · obtain ⟨e⟩ := hu.1 hlinear
    left
    refine ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2, ?_⟩
    exact ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5)).symm⟩
  · exact Or.inr (hu.2 hmathieu)
  · exact (C.not_held_normalizer_pattern D hnone z.property hz1 F hV hheld).elim

/-- The original dimension-four consumer with both source uniqueness branches
discharged. Only the independent marking and local fusion alternatives remain
explicit; no recognition, normalizer or graph-comparison input is required. -/
theorem four_recognition_of_marking_and_fusion {K : GroupClass.{u}}
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (C : SplitLinearConfiguration L V 4) (hnone : NoEscape L V)
    (compare : ∀ (z : G), z ≠ 1 → BinaryLinear.Affine.PointMarking 4 z V →
      ∃ F : TransvectionFive.MarkedCentralizer z, V = F.row ∨ V = F.column)
    (localTypes : IsSimpleGroup G → ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z →
        F.LinearFusion ∨ F.MathieuFusion ∨ F.HeldNormalizerPattern) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) :=
  four_recognition_of_source_inputs h D C hnone compare localTypes
    TransvectionFive.uniqueness_of_fusion

/-- The assembly with the §41 Mathieu branch supplied by an actual source/model
graph comparison.  The callback exposes the measured 40.3--40.5 normalizer
data and the concrete source system; it does not hide a group isomorphism in a
family tag. -/
theorem four_recognition_of_source_inputs_of_mathieu_graph {K : GroupClass.{u}}
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
      TransvectionFive.PointCoreFusion z →
      F.LinearFusion →
        Nonempty (G ≃* BinaryLinear.TransvectionFiveLocal.SL))
    (mathieuData : ∀ (z : G) (F : TransvectionFive.MarkedCentralizer z),
      TransvectionFive.PointCoreFusion z → F.MathieuFusion →
      Nonempty (TransvectionFive.MathieuSourceWitness (G := G) F)) :
    ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24) := by
  apply four_recognition_of_source_inputs h D C hnone compare localTypes
  intro hs z F hcore
  constructor
  · intro hlinear
    exact linearUnique hs z F hcore hlinear
  · intro hfusion
    obtain ⟨witness⟩ := mathieuData z F hcore hfusion
    exact TransvectionFive.mathieu_of_mathieuFusion F hs hcore hfusion witness

omit [Finite G] in
/-- Preserve the dimension in the public recognition interface. -/
theorem recognized_four_of_classical_or_mathieu
    (hG : ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    RecognizedGroup G 4 := by
  rcases hG with hG | hG
  · exact Or.inl hG
  · exact Or.inr (Or.inr ⟨rfl, hG⟩)

omit [Finite G] in
/-- The original block supplies exactly the corresponding 12.2.13 branch. -/
theorem alternatives_four_of_classical_or_mathieu
    (C : SplitLinearConfiguration L V 4)
    (hG : ClassicalGroup.IsPSL G 5 2 ∨ Nonempty (G ≃* Sporadic.Mathieu.M24)) :
    Alternatives12213 T L V := by
  rcases hG with hG | hG
  · exact Or.inr (Or.inl ⟨4, Or.inr rfl, C.block, hG⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨C.block, hG⟩))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
