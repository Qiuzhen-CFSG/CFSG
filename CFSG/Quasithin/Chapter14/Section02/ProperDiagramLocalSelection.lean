module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramLocal
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramSelection
/-!
# Local source data from the original diagram alternative

This literal consumer of the marked `DiagramModel` selects a perfect
parabolic residual.  The concrete parabolic geometry supplies its index,
Sylow intersection and two-core containment; the local supplement lemmas
then supply the C-component and Sylow assertions in its normalizer join.
The original field exponent is retained in the rank-one model.

Source: Aschbacher--Smith 14.2.8(3), printed p.983.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H : Type*} [Group H] [Finite H]
theorem source_diagram_local_residual_selection
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    [K.Normal] (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤) {f : ℕ} (hf : 1 < f)
    (hm : DiagramModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) f) :
    ∃ L : Subgroup H, L ≤ K ∧ Group.IsPerfect L ∧
      ¬L ≤ ChapterB.minimalParabolicMax T hP ∧ L ⊔ (T : Subgroup H) = ⊤ ∧
      let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
      S.relIndex (T : Subgroup H) = 2 ∧ Chapter1.IsSylowIn 2 (S ⊓ L) L ∧
      pCore 2 H ≤ S ∧ Chapter1.IsSylowIn 2 S (L ⊔ S) ∧
      (L.subgroupOf (L ⊔ S)).IsCComponent ∧
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^f) ∧
      ChapterF.Source.IsRankOneModel (L ⧸ pCore 2 L) := by
  obtain ⟨L,hLK,hperf,hout,hLT,hi,hSyl,hcore,F,hF,hfin,hchar,hcard,⟨e⟩⟩ :=
    source_diagram_residual_selection T hP hs K hK hqK hgen hf hm
  let S := (T : Subgroup H) ⊓ normalizer (L : Set H)
  have h4 : 4 ≤ Nat.card F := by
    rw [hcard]
    have hp : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at hp ⊢
    exact hp
  have hlin : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^f) :=
    ⟨F,hF,hfin,hcard,⟨e⟩⟩
  refine ⟨L,hLK,hperf,hout,hLT,hi,hSyl,hcore,?_,?_,hlin,?_⟩
  · exact sylow_in_normalized_join L S inf_le_right
      (T.isPGroup'.to_le inf_le_left) hSyl
  · exact perfect_binary_rank_one_local_component L S inf_le_right hperf h4 e
  · exact ChapterF.Source.IsRankOneModel.linear f (by omega) hlin
end CFSG.Quasithin.Chapter14.Section02
