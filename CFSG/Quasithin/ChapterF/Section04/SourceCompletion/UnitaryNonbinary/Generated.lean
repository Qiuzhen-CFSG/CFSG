module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Basic
public import Theory.GroupTheory.Amalgam.Reversal

/-!
# Full-overlap completions in the original generated subgroup

Compatible endpoint maps, including a reversed marking, transport the
inclusion completion in the join of the original endpoints. Their literal
intersection supplies the whole-overlap equality. This uses no assumption
that the original endpoints generate the ambient group.

Source: Aschbacher–Smith 5.3.1–4 and F.4.24, printed pp.658–659 and287.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
open Subgroup Theory.GroupTheory

namespace Generated
variable {G : Type*} [Group G] (P Q : Subgroup G)

abbrev amalgam : RankTwoAmalgam P (P ⊓ Q : Subgroup G) Q :=
  .ofSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right

def completion : RankTwoAmalgam.FaithfulCompletion (amalgam P Q)
    (G := (P ⊔ Q : Subgroup G)) :=
  .ofGeneratedSubgroups P (P ⊓ Q) Q inf_le_left inf_le_right

theorem whole_overlap : (completion P Q).left.range ⊓ (completion P Q).right.range =
    (completion P Q).middle.range := by
  apply le_antisymm _ (le_inf (completion P Q).middle_le_left (completion P Q).middle_le_right)
  rintro a ⟨⟨p,hp⟩,⟨q,hq⟩⟩
  have hl (p : P) : ((completion P Q).left p : G) = p :=
    RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left P (P ⊓ Q) Q
      inf_le_left inf_le_right p
  have hr (q : Q) : ((completion P Q).right q : G) = q :=
    RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right P (P ⊓ Q) Q
      inf_le_left inf_le_right q
  have hp' : (p : G) = a := (hl p).symm.trans (congrArg Subtype.val hp)
  have hq' : (q : G) = a := (hr q).symm.trans (congrArg Subtype.val hq)
  let t : (P ⊓ Q : Subgroup G) := ⟨a, hp' ▸ p.property, hq' ▸ q.property⟩
  refine ⟨t, Subtype.ext ?_⟩
  exact hl ((amalgam P Q).left t)

variable {L D R : Type*} [Group L] [Group D] [Group R]
variable {α : RankTwoAmalgam L D R}

/-- A reversed marking changes both maps, retaining the original middle. -/
def reverseCompletion {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion α.reverse (G := M)) :
    RankTwoAmalgam.FaithfulCompletion α (G := M) where
  left := c.right
  right := c.left
  compatible := c.compatible.symm
  left_injective := c.right_injective
  right_injective := c.left_injective
  middle_injective := by
    intro x y h
    apply c.middle_injective
    exact (DFunLike.congr_fun c.compatible x).trans
      (h.trans (DFunLike.congr_fun c.compatible y).symm)
  generated := by rw [sup_comm]; exact c.generated

theorem reverseCompletion_overlap {M : Type*} [Group M]
    (c : RankTwoAmalgam.FaithfulCompletion α.reverse (G := M))
    (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    (reverseCompletion c).left.range ⊓ (reverseCompletion c).right.range =
      (reverseCompletion c).middle.range := by
  change c.right.range ⊓ c.left.range = (c.right.comp α.left).range
  rw [inf_comm, hc]
  exact congrArg MonoidHom.range c.compatible

/-- The compatible isomorphism preserves the whole overlap in either orientation. -/
theorem exists_completion
    (he : Nonempty (RankTwoAmalgam.Iso (amalgam P Q) α) ∨
      Nonempty (RankTwoAmalgam.Iso (amalgam P Q) α.reverse)) :
    ∃ c : RankTwoAmalgam.FaithfulCompletion α (G := (P ⊔ Q : Subgroup G)),
      c.left.range ⊓ c.right.range = c.middle.range := by
  rcases he with he | he
  · obtain ⟨e⟩ := he
    refine ⟨(completion P Q).comapIso e.symm, ?_⟩
    simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using whole_overlap P Q
  · obtain ⟨e⟩ := he
    let c := (completion P Q).comapIso e.symm
    refine ⟨reverseCompletion c, reverseCompletion_overlap c ?_⟩
    simpa only [c, RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
      RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using whole_overlap P Q

end Generated
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
