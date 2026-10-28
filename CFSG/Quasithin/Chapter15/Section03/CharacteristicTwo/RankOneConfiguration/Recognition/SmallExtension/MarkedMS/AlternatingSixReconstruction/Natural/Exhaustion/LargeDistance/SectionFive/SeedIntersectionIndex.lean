module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.CentralLayer.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {d : Replacement L R}

include h e hz in
 theorem seed_moving_relIndex_eq_seed
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hc : color d.radical c = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (Z d.radical c).relIndex (U d.radical a) =
      (Z d.radical c).relIndex (Z d.radical a) := by
  let I := Z d.radical a ⊓ Z d.radical c
  have hUa : U d.radical a ≤ Z d.radical a := U_le_Z a
  have hZta : Z d.radical t ≤ Z d.radical a := Escape.EdgeTransfer.edge_Z_le a t ha hat
  have hZtc : Z d.radical t ≤ Z d.radical c := Escape.EdgeTransfer.edge_Z_le c t hc hct
  have hsup : U d.radical a ⊔ I = Z d.radical a := by
    apply le_antisymm (sup_le hUa inf_le_left)
    calc
      Z d.radical a = U d.radical a ⊔ Z d.radical t :=
        DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d ha hat
      _ ≤ U d.radical a ⊔ I := sup_le_sup_left (le_inf hZta hZtc) _
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a ha
  have hIN : Z d.radical a ≤ normalizer (I : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance : Z d.radical a ≤
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).trans
      (centralizer_le (show I ≤ Z d.radical a from inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  let : (I.subgroupOf (Z d.radical a)).Normal := normal_subgroupOf_of_le_normalizer hIN
  have hi := relIndex_sup_right ((U d.radical a).subgroupOf (Z d.radical a))
    (I.subgroupOf (Z d.radical a))
  rw [←subgroupOf_sup hUa (show I ≤ Z d.radical a from inf_le_left),
    relIndex_subgroupOf (sup_le hUa (show I ≤ Z d.radical a from inf_le_left)),
    relIndex_subgroupOf hUa,hsup] at hi
  have hIU : I.relIndex (U d.radical a) = (Z d.radical c).relIndex (U d.radical a) := by
    rw [←inf_relIndex_right,show I ⊓ U d.radical a = Z d.radical c ⊓ U d.radical a by
      exact inf_assoc _ _ _ |>.trans (inf_eq_right.mpr (inf_le_right.trans hUa)),
      inf_relIndex_right]
  rw [hIU] at hi
  exact hi.symm.trans (inf_relIndex_left _ _)

 theorem seed_relIndex_symm
    {a c : Vertex d.radical} (ha : color d.radical a = false)
    (hc : color d.radical c = false) :
    (Z d.radical c).relIndex (Z d.radical a) =
      (Z d.radical a).relIndex (Z d.radical c) := by
  have hcard (v : Vertex d.radical) (hv : color d.radical v = false) :
      Nat.card (Z d.radical v) = Nat.card (Z d.radical (alpha d.radical)) := by
    obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical hv
    have hv' : v = act d.radical g (alpha d.radical) := by
      simpa only [alpha,act_mVertex,one_mul] using hg
    rw [hv',Z_act,card_map_of_injective (MulAut.conj _).injective]
  let := finite_Z d.radical a
  let := finite_Z d.radical c
  let I := Z d.radical a ⊓ Z d.radical c
  let : Finite I := Finite.of_injective (inclusion (show I ≤ Z d.radical a from inf_le_left))
    (inclusion_injective _)
  have hl := (I.subgroupOf (Z d.radical a)).card_mul_index
  have hr := (I.subgroupOf (Z d.radical c)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Z d.radical a from inf_le_left)).toEquiv] at hl
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Z d.radical c from inf_le_right)).toEquiv] at hr
  change Nat.card I * I.relIndex (Z d.radical a) = Nat.card (Z d.radical a) at hl
  change Nat.card I * I.relIndex (Z d.radical c) = Nat.card (Z d.radical c) at hr
  rw [show I.relIndex (Z d.radical a) = (Z d.radical c).relIndex (Z d.radical a) from
    inf_relIndex_left _ _,hcard a ha] at hl
  rw [show I.relIndex (Z d.radical c) = (Z d.radical a).relIndex (Z d.radical c) from
    inf_relIndex_right _ _,hcard c hc] at hr
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hl.trans hr.symm)

include h e hz in
 theorem seed_moving_relIndex_symm
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t) :
    (Z d.radical c).relIndex (U d.radical a) =
      (Z d.radical a).relIndex (U d.radical c) := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  exact (seed_moving_relIndex_eq_seed (h := h) (e := e) (hz := hz) ha hc hat hct).trans
    ((seed_relIndex_symm ha hc).trans
      (seed_moving_relIndex_eq_seed (h := h) (e := e) (hz := hz) hc ha hct hat).symm)

include h e hz in
/-- A strict forward Baumann slice transfers to the opposite full seed.

The endpoint full seeds have symmetric mutual indices, while each full seed
is contained in its Baumann slice. Thus the forward strict inequality gives
the seed-index premise used by the six-letter cube calculation. -/
theorem forward_strict_seed_index
    (hb : 2 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hforward : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c)) :
    2 < (Z d.radical c).relIndex (U d.radical a) := by
  have hc : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    rw [ha] at h1
    cases ht : color d.radical t <;> cases hcc : color d.radical c <;> simp_all
  let := finite_Z d.radical a
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (U_le_Z c)) (inclusion_injective _)
  have hseed : 2 < (Z d.radical a).relIndex (U d.radical c) := by
    exact hforward.trans_le (relIndex_le_of_le_left
      (Escape.EdgeTransfer.Z_le_B hb a ha) index_ne_zero_of_finite)
  rw [seed_moving_relIndex_symm (h := h) (e := e) (hz := hz) ha hat hct]
  exact hseed

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
