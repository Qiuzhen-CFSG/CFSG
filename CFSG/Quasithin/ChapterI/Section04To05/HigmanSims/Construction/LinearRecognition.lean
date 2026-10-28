module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearInput
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeFour

/-!
# Recognition of the marked linear-three subgroup

The completed finite PSL₃(4) specialization of F.4.26 discharges the
small-completion recognition input. Applying it to the literal generated
subgroup identifies the join and preserves both endpoint ranges. The original
involutions and the compatible marking of the whole intersection, including
its odd torus, are retained.

This removes the independent recognition premise from the subgroup adapter.
Construction of the marked pair from HS1–HS2 remains a separate obligation;
no ambient generation, subgroup existence, or type-HS recognition is asserted.

Source: Aschbacher–Smith F.4.26, printed p.288, and the construction cited
at I.4.8, printed p.418.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
open ChapterF.GreenBook.LieModels

universe u

/-- The completed native theorem supplies the exact small-completion input. -/
theorem linearThreeFourSmallCompletionRecognition :
    LinearThreeFourSmallCompletionRecognition.{u} := by
  intro X _ _ c s t hs ht hsout htout hs2 ht2 hst
  exact ChapterF.SourceCompletion.LinearThreeFour.Completion.exists_parabolic_preserving_equiv_of_involutions
    c s t hs ht hsout htout hs2 ht2 hst

/-- The literal marked join is PSL₃(4), with both endpoint ranges preserved.
There is no additional completion-recognition hypothesis. -/
theorem linearThree_subgroup_of_marked_pair_recognized
    {G : Type u} [Group G] [Finite G] (P₁ P₂ : Subgroup G)
    (marking : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P₁ (P₁ ⊓ P₂) P₂ inf_le_left inf_le_right)
      (LinearThree.amalgam Matrix.PSL3Four.F))
    (s t : G) (hs : s ∈ P₁) (ht : t ∈ P₂)
    (hsout : s ∉ P₁ ⊓ P₂) (htout : t ∉ P₁ ⊓ P₂)
    (hs2 : orderOf s = 2) (ht2 : orderOf t = 2) (hst : orderOf (s * t) = 3) :
    ∃ e : (P₁ ⊔ P₂ : Subgroup G) ≃* Matrix.PSL3Four.PSL,
      (P₁.subgroupOf (P₁ ⊔ P₂)).map e.toMonoidHom =
        Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F ∧
      (P₂.subgroupOf (P₁ ⊔ P₂)).map e.toMonoidHom =
        Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F :=
  linearThree_subgroup_of_marked_pair linearThreeFourSmallCompletionRecognition
    P₁ P₂ marking s t hs ht hsout htout hs2 ht2 hst

end CFSG.Quasithin.HigmanSims
