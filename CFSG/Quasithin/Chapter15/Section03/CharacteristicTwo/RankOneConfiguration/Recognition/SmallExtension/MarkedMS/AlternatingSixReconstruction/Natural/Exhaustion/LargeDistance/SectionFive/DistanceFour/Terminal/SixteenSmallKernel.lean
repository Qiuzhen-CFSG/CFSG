module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenUnequal
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SmallKernelNormalization
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.RestrictedMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
/-!
# Restricted kernels for image-sixteen small movers

The image-sixteen Borel model transports the restricted-kernel fixedness
calculation to the actual replacement graph. The backward version applies this
calculation to the predecessor and endpoint seeds on a distance-four critical
path, preserving the literal full seeds and normalizers.

Source: MS93 (5.5)(c), (5.12)(1), printed pp.915,924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
local notation "S" => Equiv.Perm (Fin 6)
local notation "r" => Theory.SpecificGroups.SymmetricSix.BinaryFlags.pairRotation
private theorem commutator_sup_fixed {F : Type*} [Group F]
    (A E P : Subgroup F) (hEA : E ≤ normalizer (A : Set F))
    (hEP : E ≤ centralizer (P : Set F)) : ⁅A ⊔ E,P⁆ = ⁅A,P⁆ := by
  apply le_antisymm _ (commutator_mono le_sup_left le_rfl)
  apply commutator_le.mpr
  intro x hx p hp
  have hh : x ∈ (A : Set F) * (E : Set F) := by
    rw [←coe_mul_of_right_le_normalizer_left A E hEA]
    exact hx
  obtain ⟨a,ha,e,he,rfl⟩ := hh
  have hz : ⁅e,p⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hEP he p hp).symm
  rw [commutatorElement_mul_left_eq_conj_mul,hz,mul_one,mul_inv_cancel,one_mul]
  exact commutator_mem_commutator ha hp

private theorem sylow_cover_kernel_fixed
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (τ : Representation (ZMod 2) S Y)
    (hm : SixCover.IsNaturalOrCore τ (MonoidHom.id S))
    (u : S) (A P : Subgroup S) (hAP : A ≤ P)
    (hP : P ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom)
    [IsElementaryAbelian 2 P] (hne : A ≠ ⊥) :
    subspaceCommutator τ (fixedSpace τ A) P ≤
      fixedSpace τ ((D 6).map (MulAut.conj u).toMonoidHom) := by
  have hS : sylowCarrier ≤ Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj r⁻¹).toMonoidHom := by
    intro g hg
    obtain ⟨j,rfl⟩ := (mem_sylowCarrier_iff _).mp hg
    refine ⟨(MulAut.conj r) (sylowWords j),?_,?_⟩
    · have cert : ∀ j : Fin 16, (MulAut.conj r) (sylowWords j) ∈
          Theory.SpecificGroups.SymmetricSix.borel := by decide +kernel
      exact cert j
    · change r⁻¹*(r*sylowWords j*r⁻¹)*(r⁻¹)⁻¹=sylowWords j
      group
  have hB : P ≤ Theory.SpecificGroups.SymmetricSix.borel.map
      (MulAut.conj (u*r⁻¹)).toMonoidHom := by
    rw [←CubeCommonFixer.conjugate_twice]
    exact hP.trans (map_mono hS)
  have hD : Theory.SpecificGroups.SymmetricSix.BinaryFlags.D.map
      (MulAut.conj (u*r⁻¹)).toMonoidHom = (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq,←CubeCommonFixer.conjugate_twice]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (D 6 : Set S)).inv_mem CubeSmallSeeds.rotation_normalizes)
  have hh := (SixCover.BorelKernel.kernel_properties τ hm (u*r⁻¹) A P hAP hB hne).1
  rwa [hD] at hh

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem nonelementary_cover_restricted_kernel_fixed
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hb : 2 < replacementDistance h d)
    (A P : Subgroup d.overgroup) (hAP : A ≤ P) [IsElementaryAbelian 2 P]
    (hPR : P ≤ d.radical) (hnA : ¬ A ≤ pCore 2 d.overgroup) :
    ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ ≤
      centralizer (SmallMover.join (replacementMoved d) (pCore 2 d.overgroup)
        (normalizer (d.radical : Set d.overgroup)) 4 : Set d.overgroup) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let F := U ⊓ centralizer (A : Set d.overgroup)
  let H := ⁅F,P⁆
  let J := SmallMover.join U (pCore 2 d.overgroup) (normalizer (d.radical : Set d.overgroup)) 4
  obtain ⟨u,hN,_,hJ,himage,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb
  have hJimage : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    change J = _ at hJ
    rw [hJ]
    exact himage
  have hHW : H ≤ U := (commutator_mono inf_le_left le_rfl).trans (commutator_le_left _ _)
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  have hnimage : A.map s.projection ≠ ⊥ := by
    intro he
    exact hnA (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  let : IsElementaryAbelian 2 (P.map s.projection) := IsElementaryAbelian.map s.projection
  have hh := sylow_cover_kernel_fixed (coverAction s) (cover_model s) u
    (A.map s.projection) (P.map s.projection) (map_mono hAP)
    ((map_mono (hPR.trans d.radical.le_normalizer)).trans_eq hN) hnimage
  have hF : subgroupSpace U F = fixedSpace (coverAction s) (A.map s.projection) := by
    ext v
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U s.projection s.surjective hker A v).symm
  have hH : subgroupSpace U H = subspaceCommutator (coverAction s)
      (fixedSpace (coverAction s) (A.map s.projection)) (P.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker F P inf_le_left,hF]
    rfl
  rw [←hH,←hJimage] at hh
  intro v hv
  let w : Additive U := Additive.ofMul ⟨v,hHW hv⟩
  exact (mem_fixedSpace_image U s.projection s.surjective hker J w).mp (hh hv)

include e hz hn in
theorem nonelementary_edge_restricted_kernel_fixed_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hb : 2 < replacementDistance h d)
    {c t : Vertex d.radical} (hc : color d.radical c = false) (hct : Adjacent d.radical c t)
    (A P : Subgroup (FreeAmalgam d.radical)) (hAP : A ≤ P) [IsElementaryAbelian 2 P]
    (hPT : P ≤ Q d.radical t) (hnA : ¬ A ≤ Q d.radical c) :
    ⁅U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ ≤
      centralizer (SmallMover.join (U d.radical c) (Q d.radical c)
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical c) 4 : Set _) := by
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hcent hc hct
  have hPG : P ≤ stabilizer d.radical c := hPT.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical hct))
  have hPm : (P.comap i).map i = P := map_comap_eq_self (hPG.trans_eq hir.symm)
  have hAm : (A.comap i).map i = A := map_comap_eq_self ((hAP.trans hPG).trans_eq hir.symm)
  let : IsElementaryAbelian 2 (P.comap i) := IsElementaryAbelian.comap_of_injective i hi P
  have hPR : P.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hPm,hiR]
  have hnA0 : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    apply hnA
    have hm := map_mono (f := i) hh
    rwa [hAm,hiQ] at hm
  have hh := commutator_eq_bot_iff_le_centralizer.mpr
    (nonelementary_cover_restricted_kernel_fixed (e := e) (hz := hz) (hn := hn)
      hne hb (A.comap i) (P.comap i) (comap_mono hAP) hPR hnA0)
  have hiN : (normalizer (d.radical : Set d.overgroup)).map i =
      normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓ stabilizer d.radical c := by
    have he : (normalizer (d.radical.map i : Set _)).comap i = normalizer (d.radical : Set d.overgroup) := by
      rw [comap_normalizer_eq_of_le_range (map_le_range _ _),comap_map_eq_self_of_injective hi]
    rw [←he,map_comap_eq,hiR,hir,inf_comm]
  have hm := congrArg (Subgroup.map i) hh
  rw [map_commutator,map_commutator,←map_inf_centralizer_of_injective i hi,
    hiU,hAm,hPm,Subgroup.map_bot,SmallMover.join_map i hi,hiU,hiQ,hiN] at hm
  exact commutator_eq_bot_iff_le_centralizer.mp hm

include e hz hn in
theorem nonelementary_backward_kernel_mover_fixed_knownSimple
    (hne : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hb : replacementDistance h d = 4)
    {a z c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hqa : q.walk.getVert 2 = a) :
    ⁅Z d.radical c ⊓ Q d.radical (p.walk.getVert 2),Z d.radical z ⊓ Q d.radical a⁆ ≤
      centralizer (SmallMover.join (U d.radical c) (Q d.radical c)
        (normalizer (Q d.radical (q.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical c) 4 : Set _) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hcent := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let v := p.walk.getVert 2
  let t := q.walk.getVert 1
  let F := Z d.radical z ⊓ Q d.radical a
  let P := F ⊔ Z d.radical v
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    rw [←hqa]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [q.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hFt : F ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hZz : Z d.radical z ≤ Q d.radical v := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hAt : Z d.radical v ≤ Q d.radical t := by
    have hdist : (cosetGraph d.radical).dist v t < replacementDistance h d := by
      rw [SimpleGraph.dist_comm,q.dist_end,hql]
      omega
    let he := (replacementGeometry h d).exists_critical v hv
    have hcrit : (cosetGraph d.radical).dist v t <
        criticalDistance d.radical v he := by
      rw [(replacementGeometry h d).distance_constant v hv]
      exact hdist
    exact Z_le_Q_of_dist_lt d.radical v he hcrit
  have hAC : Z d.radical v ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical v q.end_color)).trans
      (centralizer_le (inf_le_left.trans hZz))
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) v q.end_color
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.sup_of_le_centralizer hAC
  let qr : CriticalPath d.radical (replacementGeometry h d) v c := {
    start_color := q.end_color
    walk := q.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hcent q }
  have hh := nonelementary_edge_restricted_kernel_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hne hb2 q.start_color hct
    (Z d.radical v) P le_sup_right (sup_le hFt hAt) qr.critical.2
  have hAF : Z d.radical v ≤ centralizer
      (U d.radical c ⊓ centralizer (Z d.radical v : Set (FreeAmalgam d.radical)) : Set _) :=
    le_centralizer_iff.mpr inf_le_right
  change ⁅U d.radical c ⊓ centralizer (Z d.radical v : Set (FreeAmalgam d.radical)),F ⊔ Z d.radical v⁆ ≤ _ at hh
  rw [commutator_comm,commutator_sup_fixed F (Z d.radical v) _
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hAF,commutator_comm] at hh
  have hfix : U d.radical c ⊓ centralizer (Z d.radical v : Set (FreeAmalgam d.radical)) =
      U d.radical c ⊓ Q d.radical v := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hcent v q.end_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) v q.end_color
        (by rw [(replacementGeometry h d).distance_constant _ q.end_color]; exact replacementDistance_pos h d)
        qr.critical (DistanceEight.U_le_Z d.radical c hx.1),hx.2⟩
    · exact inf_le_inf_left _ (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical v q.end_color)))
  have hpre : qr.walk.getVert (qr.walk.length-2) = a := by
    change q.walk.reverse.getVert (q.walk.reverse.length-2) = a
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hql]
    exact hqa
  have hFpre : F ≤ Q d.radical (qr.walk.getVert (qr.walk.length-2)) := by rw [hpre]; exact inf_le_right
  rw [hfix,←(critical_kernel_predecessor_moving s hcent hb2 qr).2.2 F hFpre] at hh
  exact hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.SixteenSmall
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
