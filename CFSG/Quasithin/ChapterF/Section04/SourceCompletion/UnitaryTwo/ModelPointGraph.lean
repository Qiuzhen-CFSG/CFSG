module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryTwo.PointGraph
/-!
# The source point-graph recognition applied to the native unitary model

Both an arbitrary completion of order25920 and the literal projective model
satisfy the same checked graph recognition. Composing their actual graph
isomorphisms supplies the comparison used for group and endpoint recognition.
Source: Aschbacher–Smith F.4.8 andF.4.24, printed pp.278 and287.
-/
public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
open SimpleGraph

lemma model_pointGraph_isSRG : modelCompletion.pointGraph.IsSRGWith 27 10 1 5 :=
  modelCompletion.pointGraph_isSRG GreenBook.LieModels.UnitaryFour.BinaryCompletion.projective_card

lemma model_pointGraph_automorphism_card_le :
    Nat.card (modelCompletion.pointGraph ≃g modelCompletion.pointGraph) ≤ 51840 :=
  (modelCompletion.pointGraph_recognition
    GreenBook.LieModels.UnitaryFour.BinaryCompletion.projective_card).2

lemma Completion.exists_model_pointGraph_iso {G : Type*} [Group G] [Finite G]
    (c : Completion G) (hcard : Nat.card G = 25920) :
    Nonempty (c.pointGraph ≃g modelCompletion.pointGraph) := by
  obtain ⟨⟨e⟩,_⟩ := c.pointGraph_recognition hcard
  obtain ⟨⟨f⟩,_⟩ := modelCompletion.pointGraph_recognition
    GreenBook.LieModels.UnitaryFour.BinaryCompletion.projective_card
  exact ⟨e.symm.trans f⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryTwo
