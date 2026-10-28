module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement.NativeBounds

/-!
# Nonquadratic movement of the entire replacement cover

If radical displacement lies in the edge seed, the entire opposite Z-layer
satisfies the maximal-plane condition. Its normal orbit lies in the base
two-core in the non-Frattini branch, contradicting critical reversal.
Thus the second commutator is nontrivial. Both statements retain the whole
central cover and require no local-image or plane-intersection premise.

Source: MS93 (3.6), printed pp.870--871. The model application is in
PlaneMovement/PointImage/Source.lean.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
open LargeDistance
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (d : Replacement L R)

include h e hz in
theorem moved_displacement_not_le_seed
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ¬ ⁅d.radical,replacementMoved d⁆ ≤ omegaCenter d.radical := by
  intro hmove
  obtain ⟨c,hc⟩ := criticalPair_exists d.radical (alpha d.radical)
    ((replacementGeometry h d).exists_critical _ rfl)
  obtain ⟨b,hab,hcb⟩ := exists_common_neighbor_of_dist_two d.radical (alpha d.radical) c
    (hc.1.trans hb)
  have hc0 := critical_endpoint_color d.radical (alpha d.radical) rfl _ hc
  have hrev := critical_reverse d.radical (replacementGeometry h d)
    (replacement_edge_centralizer h e hz d) (alpha d.radical) rfl
    (by change 0 < replacementDistance h d; omega) c hc0 hc
  obtain ⟨i,hi,hiR,hiW,hiS⟩ := edge_coordinates h e hz d hc0 hcb
  have hcomm : ⁅Q d.radical (alpha d.radical),Z d.radical c⁆ ≤ Z d.radical b := by
    apply (commutator_mono
      (Q_le_adjacent_h d.radical (DistanceTwo.NaturalCore.edge_color hab) hab) le_rfl).trans
    rw [CentralLayer.edge_displacement_eq_moving h e hz d hc0 hcb,
      ←hiR,←hiW,←hiS,←map_commutator]
    exact map_mono hmove
  have hp : Z d.radical c ≤ criticalPlane d.radical c b :=
    le_criticalPlane_of_commutator_le _ le_rfl hcomm
  exact hrev.2 (hp.trans
    ((replacement_plane_le_intersection h e hz d hb hlarge hc hab hcb).trans inf_le_right))

include h e hz in
theorem moved_double_commutator_ne_bot
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ⁅⁅d.radical,replacementMoved d⁆,d.radical⁆ ≠ ⊥ := by
  intro hzcomm
  apply moved_displacement_not_le_seed h e hz d hb hlarge
  let := replacementMoved_normal h d
  let := moved_elementary h d
  have hW : ⁅d.radical,replacementMoved d⁆ ≤ replacementMoved d := commutator_le_right _ _
  have hR : replacementMoved d ≤ d.radical :=
    (replacementMoved_le_omegaCenter h d).trans
      ((omegaCenter_le _).trans (replacement_core_le_radical h d))
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hR (hW hx),
    elemPow_eq_one_of_isElementaryAbelian (p := 2) x (hW hx),
    commutator_eq_bot_iff_le_centralizer.mp hzcomm hx⟩

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PlaneMovement
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
