module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Sylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtremality
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityExtension.FullNormalizer

/-!
# Original marked triality short-root Sylow centralizers

The native fixed-tree and Levi-projection proofs discharge model extremality
for the specified highest short root. F.4.40 then gives the designated Sylow
subgroup in its original ambient centralizer. The same root belongs to the
central radical; whole-Borel compatibility equates its left and right
transports, placing the original marker in N_G(L). No ambient order bound,
model-Sylow callback or replacement comparison is used.

Source: Aschbacher–Smith F.4.27(4)(ii), F.4.40 and the initial marking in
F.4.42, printed pp.288,294–295, with the application 5.3.3, p.659
(`refs/quasithin.pdf`). Full ambient containment remains a separate theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.LeviCommutators
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open TrialityCompletionFusion
variable {G : Type*} [Group G] [Finite G]

/-- The given right marker has the identical left transport, via the whole
Borel, and lies in the original normalizer of L. -/
theorem Preparation.triality_short_marker_left
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    ∃ v : parabolic P .central,
      v.val = short P rfl 2 1 ∧ v.val ∈ radical P .central ∧
      (e.right.symm (shortElement P rfl)).val = (e.left.symm v).val ∧
      (e.right.symm (shortElement P rfl)).val ∈ normalizer (L : Set G) := by
  let P := binaryParameters m hm
  have hr : short P rfl 2 1 ∈ radical P .central :=
    descendedRootSubgroup_le_radical P rfl .central (short_mem P rfl .central 2 trivial 1)
  have hu : short P rfl 2 1 ∈ unipotent P := by
    apply descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .central)
    exact short_mem P rfl .central 2 trivial 1
  let v : parabolic P .central := ⟨short P rfl 2 1,radical_le_parabolic P .central hr⟩
  have he : (e.right.symm (shortElement P rfl)).val = (e.left.symm v).val :=
    (congrArg Subtype.val (e.symm.right_commutes
      (⟨short P rfl 2 1,unipotent_le_borel P hu⟩ : borel P))).trans
      (congrArg Subtype.val (e.symm.left_commutes
        (⟨short P rfl 2 1,unipotent_le_borel P hu⟩ : borel P))).symm
  refine ⟨v,rfl,hr,he,?_⟩
  rw [he]
  exact (d.triality_normalizer_local_data h hH hp m hm e).left_le (e.left.symm v).property

/-- The actual marked short-root centralizer intersection with T is Sylow
in C_G(t), with the native F.4.40 premise proved internally. -/
theorem Preparation.triality_short_centralizer_sylow
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.Triality.amalgam (binaryParameters m hm)).reverse) :
    let P := binaryParameters m hm
    let t : G := (e.right.symm (shortElement P rfl)).val
    ∃ R : Sylow 2 (centralizer ({t} : Set G)),
      (R : Subgroup _) = (T : Subgroup G).subgroupOf (centralizer ({t} : Set G)) := by
  let P := binaryParameters m hm
  have hm2 := (d.triality_local_structure h hH.1.1.2 hp m hm e).2.1
  apply d.triality_involution_centralizer_sylow h hH hp m hm e (shortElement P rfl)
  · apply descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P rfl .central)
    exact short_mem P rfl .central 2 trivial 1
  · exact (Subgroup.orderOf_coe (shortElement P rfl)).symm.trans
      (_root_.Triality.Standard.ShortRootCentralizer.short_order P rfl 1 one_ne_zero)
  · exact _root_.Triality.Standard.ShortRootCentralizer.centralizer_sylow m hm hm2 1 one_ne_zero

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
