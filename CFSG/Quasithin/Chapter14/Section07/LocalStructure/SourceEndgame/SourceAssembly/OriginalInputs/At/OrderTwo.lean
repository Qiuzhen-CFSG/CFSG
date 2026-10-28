module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Selection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceReversal

/-!
# The actual critical star image has order two

The two original cores generate R₁, so the critical actor lies in the
marked upper Sylow. Coordinate re-marking supplies the Borel actors and
the literal section duality. The reversed critical path constructed from
the same G,T exchanges the ranks. The three possible fixed-core orders
are then excluded by the proved fusion and centralizer conclusions of
14.7.68. This proves source 14.7.69 with the chosen path and the original
star map, and constructs a selected path satisfying it.
The earlier structural, faithful and A₅ module inputs retain their original
producers; final assembly remains with qt-d-14775-source.
Source: AS 14.7.4(4), 14.7.66–69, pp.1043,1070–1073.
-/

public noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem core_le_sylow (H : Subgroup G) (hT : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow H (T.subtype hT)).trans_eq (map_subgroupOf_eq_of_le hT)



/-- The original two-cores generate the point-parabolic two-core. -/
theorem Data.source_core_product_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    Q T L ⊔ F.H.pCoreIn 2 = F.Ri L 1 := by
  let J := L ⊔ (T : Subgroup G)
  let R := (F.Ri L 1).subgroupOf J
  let N := (F.H.pCoreIn 2).subgroupOf J
  let D := (F.Li L 1).subgroupOf J
  have hRJ : F.Ri L 1 ≤ J := (pCoreIn_le 2 _).trans Rechoice.group_le_LT
  have hNJ : F.H.pCoreIn 2 ≤ J := (core_le_sylow F.H (F.invariant 1)).trans le_sup_right
  have hDJ : F.Li L 1 ≤ J := (F.Li_le L 1).trans (inf_le_left.trans le_sup_left)
  obtain ⟨e,q,hq,hq2,ha,hker,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSourceAt.exists_marking d.natural F structural
  have hkerMap : q.ker.map J.subtype = Q T L := by
    rw [hker, subgroupOf_map_subtype, inf_comm]
    exact d.natural.centralizer_LT_at structural
  have hNle : N.map q ≤ Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    rw [←hR]
    exact map_mono (subgroupOf_mono J (d.source_QH_le_Ri))
  have hn : D ≤ normalizer (N : Set J) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro x
    change (x : G) ∈ F.H.pCoreIn 2 ↔
      (a : G) * (x : G) * (a : G)⁻¹ ∈ F.H.pCoreIn 2
    exact mem_normalizer_iff.mp
      ((F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H)))
          ((F.Li_le L 1 ha).2)) _
  have hlarge : 2 < Nat.card (N.map q) := by
    by_contra hc
    have hDN := commutator_le_ker_of_normalized_image_card_le_two q D N hn (by omega)
    have hDNQ : ⁅F.Li L 1,F.H.pCoreIn 2⁆ ≤ Q T L := by
      have hh := map_mono (f := J.subtype) hDN
      rw [map_commutator, map_subgroupOf_eq_of_le hDJ,
        map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
      exact hh
    have hQV : Q T L ≤ centralizer (V : Set G) := by
      change (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ _
      rw [← d.natural.centralizer_LT_at structural]
      exact inf_le_right
    have hpoint : F.H ≤ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
    have h1 : ⁅⁅F.Li L 1,F.H.pCoreIn 2⁆,V⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (hDNQ.trans hQV)
    have h2 : ⁅⁅F.H.pCoreIn 2,V⁆,F.Li L 1⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      have hp : ⁅F.H.pCoreIn 2,V⁆ ≤ F.Vi 1 := by
        rw [commutator_comm]
        exact (commutator_mono (V_le_U F) le_rfl).trans hcomm
      exact hp.trans (le_centralizer_iff.mp ((F.Li_le L 1).trans (inf_le_right.trans hpoint)))
    have hz := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [←d.seed_eq_commutator_point_residual] at hz
    exact hmove ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)).trans
      (centralizer_le (F.le_seed 2)))
  have hc : Nat.card (N.map q) = 4 := by
    have hd := card_dvd_of_le hNle
    rw [Matrix.PSL3Two.MarkedAutomorphisms.card_pointV] at hd
    have hb := Nat.le_of_dvd (by decide : 0 < 4) hd
    interval_cases h : Nat.card (N.map q) <;> norm_num [h] at *
  have he : N.map q = R.map q := by
    rw [hR]
    exact eq_of_le_of_card_ge hNle (by rw [hc, Matrix.PSL3Two.MarkedAutomorphisms.card_pointV])
  have hRN : R ≤ N ⊔ q.ker := by
    rw [←comap_map_eq]
    exact (map_le_iff_le_comap).mp he.ge
  have hh := map_mono (f := J.subtype) hRN
  rw [map_subgroupOf_eq_of_le hRJ, Subgroup.map_sup, map_subgroupOf_eq_of_le hNJ, hkerMap] at hh
  exact le_antisymm (sup_le d.source_Q_le_Ri d.source_QH_le_Ri) (by simpa [sup_comm] using hh)


/-- The literal star quotient kills Q_H and preserves the product identity. -/
theorem Data.source_Q_star_eq_Ri_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    star F (Q T L) = star F (F.Ri L 1) := by
  have he := congrArg (fun A : Subgroup G => star F A)
    (d.source_core_product_at structural hcomm hmove)
  change ((Q T L ⊔ F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = _ at he
  rw [subgroupOf_sup (Q_le_H F) (pCoreIn_le 2 F.H), Subgroup.map_sup] at he
  have hz : ((F.H.pCoreIn 2).subgroupOf F.H).map (starMap F) = ⊥ := by
    change (((pCore 2 F.H).map F.H.subtype).comap F.H.subtype).map (starMap F) = ⊥
    rw [comap_map_eq_self_of_injective F.H.subtype_injective,
      Subgroup.map_eq_bot_iff, starMap, QuotientGroup.ker_mk']
  simpa only [star,hz,sup_bot_eq] using he


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Rechoice.Goldschmidt.LeftChiefFactors
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors

private theorem root_sylow (r : ChapterJ.L2FourAction) :
    Chapter1.IsSylowIn 2 (BorelRefinements.root r) (alternatingGroup (Fin 5)) := by
  let P := Matrix.SpecialLinearGroup.upperUnipotentSylow SL2FourNatural.F 2
  have hP : Chapter1.IsSylowIn 2 U0 (⊤ : Subgroup SL) := by
    apply Chapter1.isSylowIn_iff.mpr
    refine ⟨P.isPGroup', le_top, ?_⟩
    intro B hB hPB _
    exact P.is_maximal' hB hPB
  have hm := (Chapter1.IsSylowIn.map_iff (BorelRefinements.markingHom r)
    (BorelRefinements.markingHom_injective r)).mpr hP
  have he : (⊤ : Subgroup SL).map (BorelRefinements.markingHom r) =
      alternatingGroup (Fin 5) := by
    rw [BorelRefinements.markingHom, ← map_map,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr r.marking.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [he] at hm
  exact hm

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original R₁ image is a Sylow subgroup of the original K image. -/
theorem Data.source_Ri_star_sylow_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F)) := by
  let d' := BorelRefinements.upperRemark_at d structural
  have hm := BorelRefinements.upperRemark_upperMarking_at d structural
  have hs := root_sylow d'.naturalQuotient
  apply (Chapter1.IsSylowIn.map_iff d.model.toMonoidHom d.model.injective).mp
  have hR : (star F (F.Ri L 1)).map d.model.toMonoidHom =
      BorelRefinements.root d'.naturalQuotient := by
    rw [star, map_map]
    exact hm
  have hK : (star F (K F)).map d.model.toMonoidHom = alternatingGroup (Fin 5) := by
    rw [star, map_map]
    exact d.K_image
  rw [hR,hK]
  exact hs

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
/-- Reverse the original critical path while retaining both U and point markings. -/
theorem earlierSymmetry_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) : d.EarlierSymmetry := by
  intro c earlier selection hr
  obtain ⟨r⟩ := exists_geometry_of_star_ne_bot_at d structural c (c.Uα_le_H earlier)
    (d.critical_star_nontrivial_at structural hcomm c)
  have he := d.source_earlierImages_at structural r.path earlier.image_eq earlier.sylow
  have hs : r.path.RankSelection := {
    positive := by
      rw [r.reverse_index earlier]
      exact lt_of_lt_of_le selection.positive selection.comparison
    comparison := by
      rw [r.reverse_index earlier,r.reverse_star he]
      exact hr.symm.le }
  exact ⟨⟨r.path,r.conjugator,r.conjugator_mem,r.base_U,r.tip_U,r.base_point,r.tip_point,he,hs⟩⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Subgroup Representation Chapter12.Section08 Rechoice.Goldschmidt
open Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Chapter13.Section03.SourceCompletion
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d
/-- Source 14.7.69 on the literal critical actor, with all local inputs constructed. -/
theorem order_two_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (five : OriginalAlternatingFiveModules1332At T L)
    (c : CriticalPath (L := L) F) (selection : c.RankSelection) :
    Nat.card (star F c.Uα) = 2 := by
  let d' := upperRemark_at d structural
  have hc := d'.sectionCentralizer_from_flag
  have hcomm := d'.U_core_commutator_eq_point_of_original_modules_at five
  have hmove := d'.plane_noncentrality_of_original_modules_at five
  obtain ⟨X,aX,mX,hs⟩ := CriticalIntersections.exists_sourceDuality d' hc
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  have himage := d'.source_Q_star_eq_Ri_at structural hcomm.le hmove
  have earlier := d'.source_earlierImages_at structural c himage (d'.source_Ri_star_sylow_at structural)
  have mark := upperRemark_upperMarking_at d structural
  have borel := compatibleBorel_of_upperMarking_at d' structural mark
  obtain ⟨fusion,centralizers⟩ := d'.source_lemma_14_7_68_from_original_modules_at structural faithful five
  exact d'.lemma_14_7_69 hc (Rechoice.SourceCompletion.moduleSeparation d') s
    (fun a ha b => b.localActors_of_marked_source ha mark borel)
    (SourceReversal.earlierSymmetry_at d' structural hcomm) hcomm fusion centralizers
    c earlier (c.sourceSelection_of_rank d' selection) (d'.source_reciprocal_placement c)

/-- Choose the actual path and prove its order-two image before the final rechoice. -/
theorem exists_order_two_criticalPath_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (five : OriginalAlternatingFiveModules1332At T L) :
    ∃ c : CriticalPath (L := L) F, c.EarlierImages ∧ c.RankSelection ∧
      Nat.card (star F c.Uα) = 2 := by
  obtain ⟨c,hc⟩ := d.exists_selected_criticalPath_from_original_modules_at structural five
  have he := d.source_earlierImages_at structural c
    (d.source_Q_star_eq_Ri_at structural
      (d.U_core_commutator_eq_point_of_original_modules_at five).le
      (d.plane_noncentrality_of_original_modules_at five))
    (d.source_Ri_star_sylow_at structural)
  exact ⟨c,he,hc,d.order_two_from_original_modules_at structural faithful five c hc⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
