module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.Action
public import Theory.GroupTheory.Amalgam.GeneratedCompletion
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Tree

/-!
# Faithfulness of the reduced universal coset tree

The reduced F.1.1 pair already gives a faithful triple in its actual generated
group. The literal subgroup-inclusion completion has trivial middle core.
Transport of normal subgroups in a marked middle transfers this property to
the universal completion. Its exact endpoint intersection identifies the
kernel of the universal coset action. No geometric or finite recognition
premise is needed.

Source: DGS, *Groups and Graphs* (1985), the tree reduction used in (15.2),
p.227, and Aschbacher--Smith F.1.9. This uses the proved source triple and
preserves the original reduced Borel, including its odd part.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The reduced universal overlap has trivial normal core, directly from
the genuine original F.1.1 hypotheses. -/
theorem reduced_universal_core_eq_bot (h : HypothesisF11 L S) :
    ((Universal.left (reducedAmalgam L S)).range ⊓
      (Universal.right (reducedAmalgam L S)).range).normalCore = ⊥ := by
  let d : FaithfulCompletion (reducedAmalgam L S)
      (G := (parabolic L (reducedSylow L S) 0 ⊔ parabolic L (reducedSylow L S) 1 : Subgroup G)) :=
    FaithfulCompletion.ofGeneratedSubgroups _ _ _
      (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
  have hdMiddle : d.middle = inclusion
      (show commonBorel L (reducedSylow L S) ≤
        parabolic L (reducedSylow L S) 0 ⊔ parabolic L (reducedSylow L S) 1 from
          (commonBorel_le_parabolic 0).trans le_sup_left) := by
    apply MonoidHom.ext
    intro b
    apply Subtype.ext
    exact FaithfulCompletion.ofGeneratedSubgroups_left _ _ _
      (commonBorel_le_parabolic 0) (commonBorel_le_parabolic 1)
      ((reducedAmalgam L S).left b)
  have hdB : d.middle.range = (commonBorel L (reducedSylow L S)).subgroupOf
      (parabolic L (reducedSylow L S) 0 ⊔ parabolic L (reducedSylow L S) 1) := by
    rw [hdMiddle]
    exact inclusion_range _
  have hd : d.middle.range.normalCore = ⊥ := by
    rw [hdB, parabolics_generate]
    exact (reduced_hypothesis h).generatedLocallyRankOneTriple.faithful _ inferInstance
      ((commonBorel L (reducedSylow L S)).subgroupOf
        (generated L (reducedSylow L S))).normalCore_le
  have hc := (Universal.completion (reducedAmalgam L S) d).middle_normalCore_eq_bot_of_model d hd
  rw [Universal.overlap_eq (reducedAmalgam L S)
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  exact hc
end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
