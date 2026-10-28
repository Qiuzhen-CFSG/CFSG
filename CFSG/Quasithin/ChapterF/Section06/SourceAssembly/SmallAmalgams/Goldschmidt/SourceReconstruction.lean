module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.SourceCuts
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.Reorientation
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.G2NormalBase
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.Goldschmidt.MathieuNormalBase

/-!
# Reconstructing either orientation of the original marked pair

The proved G₂ and Mathieu normal-base extension theorems apply in either
orientation of the same universal tree. Transport back along its marked
embedding preserves the common overlap map, including when the vertices
are interchanged. This discharges the reconstruction cut without a size
or abstract-local-isomorphism assumption.

Source: Goldschmidt (1980), (3.2), (3.7)--(3.8), pp.386--392.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open GreenBook RankTwoAmalgam
universe u

private def swappedIso {G H : Type*} [Group G] [Group H]
    {A B : Subgroup G} {C D : Subgroup H}
    (e : Iso (inclusionAmalgam A B) (inclusionAmalgam C D)) :
    Iso (inclusionAmalgam B A) (inclusionAmalgam D C) where
  left := e.right
  middle := (MulEquiv.subgroupCongr (inf_comm B A)).trans
    (e.middle.trans (MulEquiv.subgroupCongr (inf_comm C D)))
  right := e.left
  left_commutes x := e.right_commutes ⟨x.val, x.property.2, x.property.1⟩
  right_commutes x := e.left_commutes ⟨x.val, x.property.2, x.property.1⟩

private theorem exceptional_of_iso {G H : Type*} [Group G] [Group H]
    {A B : Subgroup G} {C D : Subgroup H}
    (e : Iso (inclusionAmalgam A B) (inclusionAmalgam C D))
    (h : ExceptionalMarkedAmalgam C D) : ExceptionalMarkedAmalgam A B := by
  rcases h with ⟨E⟩ | ⟨E⟩ | ⟨E⟩ | ⟨E⟩
  · exact Or.inl ⟨e.trans (Classical.choice E)⟩
  · exact Or.inr (Or.inl ⟨e.trans (Classical.choice E)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans (Classical.choice E)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans (Classical.choice E)⟩))

/-- Reconstruct either marked orientation on the same, possibly infinite,
ambient tree action. Only the local stabilizers must be finite. -/
theorem exceptional_of_marked_residual {G : Type u} [Group G]
    {F : Bool → Subgroup G} (h : CubicTreeAction F)
    (hm : DerivedMarkedBase (residualFamily F) ∨ MathieuMarkedBase (residualFamily F)) :
    ExceptionalMarkedAmalgam (F false) (F true) ∨
      ExceptionalMarkedAmalgam (F true) (F false) := by
  rcases hm with (⟨e⟩ | ⟨e⟩) | (⟨e⟩ | ⟨e⟩)
  · rcases GreenBook.Goldschmidt.G2NormalBase.classification_of_residual_iso h (Classical.choice e) with hi | hf
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr (Or.inl hf))
  · rcases GreenBook.Goldschmidt.G2NormalBase.classification_of_residual_iso h.swap (Classical.choice e) with hi | hf
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr (Or.inl hf))
  · rcases GreenBook.Goldschmidt.MathieuNormalBase.classification_of_residual_iso h (Classical.choice e) with hi | ho
    · exact Or.inl (Or.inr (Or.inr (Or.inl hi)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ho)))
  · rcases GreenBook.Goldschmidt.MathieuNormalBase.classification_of_residual_iso h.swap (Classical.choice e) with hi | ho
    · exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ho)))

/-- Discharge the normal-base reconstruction cut on the literal universal
completion of the original finite triple. -/
theorem normalBaseReconstruction : NormalBaseReconstructionInput.{u} := by
  intro G _ _ A B S h hcore _ _ _ _ _ _
  dsimp only
  intro hm
  let e := Universal.markedIso (inclusionAmalgam A B)
    (Subgroup.inclusion_injective inf_le_left) (Subgroup.inclusion_injective inf_le_right)
  rcases exceptional_of_marked_residual
      (universalCubicTreeAction_of_goldschmidt h hcore) hm with hAB | hBA
  · exact Or.inl (exceptional_of_iso e hAB)
  · exact Or.inr (exceptional_of_iso (swappedIso e) hBA)

/-- Only the four geometric and marked-recognition source arguments remain;
the extension step is supplied by the proved reconstruction theorem. -/
theorem largeNonabelian_of_geometric_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (three : RadiusThreeMarkedInput.{u}) :
    LargeNonabelianMarkedAmalgamInput.{u} :=
  largeNonabelian_of_source_cuts labels radius two three normalBaseReconstruction

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
