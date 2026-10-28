module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ResidualSelectors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneFourSpans
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRestrictedActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneLargeShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFourExclusion

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

/-!
# Adjusted seeds for large critical images on both covers

For a large critical pair in the original cubic graph, restrict its moving
cover by at most a factor of two while preserving the critical commutator.
Adjoining the entire last-edge seed gives an actor inside the full endpoint
seed. This actor retains that central attachment and the whole critical
commutator, and controls the restricted radius on both moving covers.

In the Borel case its even involution selects a proper Thompson mover that
generates the whole stabilizer with this actor. The first-edge seed commutes
with the actor, so the same selection supplies the full fixed-subgroup
comparison. A residual representative transports both incident vertices;
the radius control then proves backward criticality and normalization of the
full restricted backward kernel joined to the starting seed.

The restriction addresses the two-transposition exception in MS93 (3.3)(ii)(1)
and the adjusted actor introduced in (5.0). It does not assert normalization
by the full endpoint seed on the order-thirty-two cover. Initial small-image
compatibility and the distance-four terminal contradiction remain separate.
The original cubic kernel E and its odd quotient E/Q are retained throughout.
OriginalSylowExceptional applies both results to the literal c.L,d.S graph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.0), (5.5)--(5.8) and the normalization step in (5.12),
printed pp.866--867,912,916--920,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

local notation "M" => (L ⊔ R : Subgroup G)

private theorem large_core_moving_restriction
    (hcore : Nat.card (initialMoved L R) = 32) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hforward : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    ∃ W : Subgroup (FreeAmalgam Rg), W ≤ U Rg a' ∧
      W.relIndex (U Rg a') ≤ 2 ∧
      ⁅U Rg (alpha Rg),W⁆ = ⁅U Rg (alpha Rg),U Rg a'⁆ ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z Rg (alpha Rg) ∧
      ∃ a ∈ (W.comap (embedM Rg)).map π,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  have hb := distance_gt_two h e hz hk
  let a := alpha Rg
  have hl : 2 < p.walk.length := by rw [p.length_eq_b]; exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent Rg a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [p.end_color] at hh
    cases he : color Rg t <;> simp_all
  have het : Adjacent Rg (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-2))
  have hYt : Y ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht het)
  have hY : Y ≤ stabilizer Rg a' := fun _ hx =>
    (hYt hx).2 _ (adjacent_symm Rg hct)
  have hcomm : ⁅U Rg a',U Rg a⁆ ≤ ⁅Z Rg a,Z Rg a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono (DistanceEight.U_le_Z Rg a) (DistanceEight.U_le_Z Rg a')
  have hRZa : ⁅Z Rg a,Z Rg a'⁆ ≤ Z Rg a :=
    (critical_seed_commutator_le h p).trans inf_le_left
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let : IsElementaryAbelian 2 (U Rg a) := IsElementaryAbelian.of_le (DistanceEight.U_le_Z Rg a)
  have hAA : ⁅U Rg a',U Rg a⁆ ≤
      centralizer (U Rg a : Set (FreeAmalgam Rg)) :=
    (hcomm.trans hRZa).trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (show (U Rg a : Set (FreeAmalgam Rg)) ⊆ Z Rg a from DistanceEight.U_le_Z Rg a)))
  have hAY : ⁅U Rg a',U Rg a⁆ ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes h p hb))
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a' p.end_color
  have hA : U Rg a ≤ i.range := by
    rw [hir]
    exact (DistanceEight.U_le_Z Rg a).trans (Z_le_stabilizer_of_dist_le a _ p.critical.1.le)
  have hforwardU := critical_forward_moving_image_four_le h e hz hk p hforward
  obtain ⟨W,hW,hindex,hpres,hcontrol⟩ := embedded_cover_restriction_preserving h e hz hk i hi (U Rg a) hA
    (hiQ.symm ▸ hforwardU) (hiU.symm ▸ hAA)
  have hWU : W ≤ U Rg a' := hiU ▸ hW
  have hbound : ⁅Y,W⁆ ≤ Z Rg a := by
    rw [commutator_comm]
    have hh := hcontrol Y (hY.trans_eq hir.symm) (hiU.symm ▸ hAY)
    rw [hiU] at hh
    exact hh.trans (hcomm.trans hRZa)
  have hUbase : U Rg a' ≤ (embedM Rg).range := by
    change U Rg a' ≤ Mbar Rg
    rw [←stabilizer_m_base Rg]
    exact (DistanceEight.U_le_Z Rg a').trans
      (critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
        (sourceDistance_pos h) p.critical)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  let : IsElementaryAbelian 2 (U Rg a') := IsElementaryAbelian.of_le (DistanceEight.U_le_Z Rg a')
  have hqreverse : ⁅U Rg a,U Rg a'⁆ ≤
      centralizer (U Rg a' : Set (FreeAmalgam Rg)) :=
    ((commutator_mono (DistanceEight.U_le_Z Rg a) (DistanceEight.U_le_Z Rg a')).trans
      (by
        rw [commutator_comm]
        exact (critical_seed_commutator_le h (CriticalPath.ofPair p.end_color (reverse_pair h e p))).trans inf_le_left)).trans
        ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
          (centralizer_le (DistanceEight.U_le_Z Rg a')))
  have hpresreverse : ⁅U Rg a,W⁆ = ⁅U Rg a,U Rg a'⁆ := by
    rw [commutator_comm,commutator_comm (U Rg a)]
    exact hiU ▸ hpres
  have hr := reverse_critical_moving_image_four_le h e hz hk p hforward
  have hQbase := Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
  have hU := (graph_U_map h e hz).symm
  obtain ⟨c,hcW,hc2,hceven⟩ := embedded_preserving_actor_even h e hz hk hcore
    (embedM Rg) (embedM_injective Rg) (U Rg a') W hUbase hWU
    (hQbase ▸ hr) (hU ▸ hqreverse) (hU ▸ hpresreverse)
  exact ⟨W,hWU,hiU ▸ hindex,hpresreverse,hbound,c,hcW,hc2,hceven⟩

include h e hz hk in
private theorem large_moving_restriction
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ W : Subgroup (FreeAmalgam Rg), W ≤ U Rg z ∧
      W.relIndex (U Rg z) ≤ 2 ∧
      ⁅U Rg (alpha Rg),W⁆ = ⁅U Rg (alpha Rg),U Rg z⁆ ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z Rg (alpha Rg) ∧
      ∃ a ∈ (W.comap (embedM Rg)).map π,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  rcases moved_card h e hz hk with hnat | hcore
  · obtain ⟨a,ha,ha2,heven⟩ := critical_moving_even_actor h e hz hk p hp
    exact ⟨U Rg z,le_rfl,by simp,rfl,
      critical_radius_moving_commutator_le_Z_of_natural h e hz hk hnat
        (distance_gt_two h e hz hk) p hp,a,ha,ha2,heven⟩
  · exact large_core_moving_restriction h e hz hk hcore p hp

include h e hz in
private theorem critical_whole_commutator_eq_moving
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hb : 2 < sourceDistance h) :
    ⁅Z Rg a,Z Rg z⁆ = ⁅U Rg a,U Rg z⁆ := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hab : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hlast := terminal_last_edge_inputs h p hb
  have hbc : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hab
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have htc : color Rg (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne Rg hlast.1
    rw [p.end_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hzQb : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant _ p.end_color]
    change p.walk.length-1 < sourceDistance h
    omega
  have haQt : Z Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-1)) := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical _ p.start_color)
    rw [p.dist_start (Nat.sub_le _ _),(sourceGeometry h).distance_constant _ p.start_color]
    change p.walk.length-1 < sourceDistance h
    omega
  have haG : Z Rg a ≤ stabilizer Rg z := Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hzG : Z Rg z ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical
  have hfirst := commutator_eq_of_centralizing_sup
    ((sup_comm (Z Rg (p.walk.getVert 1)) (U Rg a)).trans
      (vertex_seed_eq_moving_sup_edge h e hz p.start_color hab).symm)
    ((terminal_edge_seed_central hbc).trans (centralizer_le hzQb))
    (((DistanceEight.U_le_Z Rg a).trans haG).trans (Z_normalized Rg z))
  have hsecond := commutator_eq_of_centralizing_sup
    ((sup_comm (Z Rg (p.walk.getVert (p.walk.length-1))) (U Rg z)).trans
      (vertex_seed_eq_moving_sup_edge h e hz p.end_color hlast.1).symm)
    ((terminal_edge_seed_central htc).trans
      (centralizer_le ((DistanceEight.U_le_Z Rg a).trans haQt)))
    (((DistanceEight.U_le_Z Rg z).trans hzG).trans (U_normalized a))
  rw [commutator_comm (Z Rg z) (U Rg a),
    commutator_comm (Z Rg z) (Z Rg a)] at hfirst
  exact hfirst.symm.trans hsecond.symm

include h e hz hk in
/-- An adjusted full seed for a large critical pair, on either moving cover.
It retains the entire last-edge seed, has index at most two in the full
endpoint seed, and preserves the whole critical commutator. Its control
and actual even image are constructed, not supplied as extra premises. -/
theorem large_critical_adjusted_seed
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ Z Rg z ∧
      Z Rg (p.walk.getVert (p.walk.length-1)) ≤ A ∧
      A.relIndex (Z Rg z) ≤ 2 ∧
      ⁅Z Rg (alpha Rg),A⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ ∧
      ⁅V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z Rg (alpha Rg) ∧
      ∃ a ∈ (A.comap (embedM Rg)).map π,
        orderOf a = 2 ∧ a ∈ alternatingGroup (Fin 6) := by
  obtain ⟨W,hWU,hi,hpres,hcontrol,a,ha,ha2,heven⟩ := large_moving_restriction h e hz hk p hp
  let t := p.walk.getVert (p.walk.length-1)
  let A := W ⊔ Z Rg t
  let Y := V Rg (alpha Rg) ⊓ Q Rg (p.walk.getVert (p.walk.length-2))
  have hb := distance_gt_two h e hz hk
  have ht := terminal_last_edge_inputs h p hb
  have htcol : color Rg t = true := by
    have hh := adjacent_color_ne Rg ht.1
    rw [p.end_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hgen := vertex_seed_eq_moving_sup_edge h e hz p.end_color ht.1
  have htZ : Z Rg t ≤ Z Rg z := hgen ▸ le_sup_right
  have hWZ : W ≤ Z Rg z := hWU.trans (DistanceEight.U_le_Z Rg z)
  have hAZ : A ≤ Z Rg z := sup_le hWZ htZ
  have hZG : Z Rg z ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl (sourceDistance_pos h) p.critical
  have hUA : U Rg z ⊔ A = Z Rg z := by
    dsimp only [A]
    rw [←sup_assoc,sup_of_le_left hWU,←hgen]
  have hindex : A.relIndex (Z Rg z) ≤ 2 := by
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
    let : (A.subgroupOf (Z Rg z)).Normal := normal_of_isMulCommutative _
    have hidx := relIndex_sup_left ((U Rg z).subgroupOf (Z Rg z)) (A.subgroupOf (Z Rg z))
    rw [←subgroupOf_sup hAZ (DistanceEight.U_le_Z Rg z),sup_comm A (U Rg z),hUA,
      relIndex_subgroupOf le_rfl,relIndex_subgroupOf (DistanceEight.U_le_Z Rg z)] at hidx
    rw [hidx]
    let := finite_Z Rg z
    let : Finite (U Rg z) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z Rg z)) (inclusion_injective _)
    exact (relIndex_le_of_le_left (show W ≤ A from le_sup_left) (by exact index_ne_zero_of_finite)).trans hi
  have hpres' : ⁅Z Rg (alpha Rg),A⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ := by
    apply le_antisymm (commutator_mono le_rfl hAZ)
    rw [critical_whole_commutator_eq_moving h e hz p hb,←hpres]
    exact commutator_mono (DistanceEight.U_le_Z Rg (alpha Rg)) le_sup_left
  have hAY : ⁅Y,A⁆ ≤ Z Rg (alpha Rg) := by
    rw [commutator_comm]
    exact commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg)) W (Z Rg t) Y
      (Z Rg (alpha Rg)) (Z_normalized Rg _) (hWZ.trans hZG) (htZ.trans hZG)
      (by rw [commutator_comm]; exact hcontrol)
      ((commutator_eq_bot_iff_le_centralizer.mpr
        ((terminal_edge_seed_central htcol).trans
          (centralizer_le (inf_le_right.trans ht.2.1)))).le.trans bot_le)
  exact ⟨A,hAZ,le_sup_right,hindex,hpres',hAY,a,
    (map_mono (comap_mono (show W ≤ A from le_sup_left))) ha,ha2,heven⟩

include h e hz hk in
private theorem borel_even_actor_generating_mover
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (A : Subgroup (FreeAmalgam Rg)) (hAG : A ≤ stabilizer Rg (alpha Rg))
    (a : S) (ha : a ∈ (A.comap (embedM Rg)).map π)
    (ha2 : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ edgeOffenderJoin (alpha Rg) t ⊔ A = stabilizer Rg (alpha Rg) := by
  let := h.relative_normal
  let F₀ := borelPlane h e hz hk u
  let A₀ := A.comap (embedM Rg)
  have hmapA : A₀.map (embedM Rg) = A := map_comap_eq_self
    (hAG.trans_eq (stabilizer_m_base Rg))
  obtain ⟨k,hkgen⟩ := PlaneSelection.even_actor_choices
    u ⟨a,haeven⟩ (by simpa only [Subgroup.orderOf_mk] using ha2)
  have hkL : k.val ∈ (L.subgroupOf (L ⊔ R)).map π := by
    rw [CubicAction.component_image h e hz hk]
    exact k.property
  obtain ⟨g,hg,hgk⟩ := hkL
  have hm : (F₀.map (MulAut.conj g).toMonoidHom).map π =
      (F₀.map π).map (MulAut.conj k.val).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change π (g*x*g⁻¹) = k.val*π x*k.val⁻¹
    rw [map_mul,map_mul,map_inv,hgk]
  have hQ : (pCore 2 M).map (MulAut.conj g).toMonoidHom = pCore 2 M :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  let F := F₀.map (MulAut.conj g).toMonoidHom ⊔ A₀
  have hQF : pCore 2 M ≤ F := by
    rw [←hQ]
    exact (map_mono (borelPlane_core_le h e hz hk u)).trans le_sup_left
  have hD : D.map (MulAut.conj u).toMonoidHom = F₀.map π :=
    (borelPlane_image h e hz hk u hR).symm
  have hfullF : F.map π = ⊤ := by
    rw [Subgroup.map_sup,hm]
    apply top_unique
    rw [←hkgen]
    exact sup_le_sup (map_mono hD.le) (zpowers_le.mpr ha)
  have hFE : F ⊔ extensionKernel h = ⊤ := by
    have he := congrArg (Subgroup.comap π) hfullF
    rwa [comap_map_eq,CubicAction.projection_kernel h e hz hk,comap_top] at he
  have hEF : extensionKernel h ≤ F := by
    have he := extensionKernel_no_supplement h F (hFE ▸ le_top)
    rw [extensionKernel_twoCore h,sup_of_le_left hQF] at he
    exact he
  have hgen : F₀.map (MulAut.conj g).toMonoidHom ⊔ A₀ = ⊤ := by
    change F = ⊤
    rwa [sup_of_le_left hEF] at hFE
  let f := (embedM Rg g)⁻¹
  have hf : f ∈ stabilizer Rg (alpha Rg) := by
    change f ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have hfix : act Rg f (alpha Rg) = alpha Rg := hf
  have hbaseJ := remaining_join_in_chart h e hz hk u (Or.inr hR) rfl
    (base_adjacent Rg) (embedM Rg) (embedM_injective Rg) (Q_beta Rg).symm
    (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
    (graph_U_map h e hz)
  have hJ := remaining_edge_join_act h e hz hk u (Or.inr hR) rfl (base_adjacent Rg) f
  change edgeOffenderJoin (act Rg f (alpha Rg)) (act Rg f (beta Rg)) =
    (edgeOffenderJoin (alpha Rg) (beta Rg)).map
      (MulAut.conj f⁻¹).toMonoidHom at hJ
  change edgeOffenderJoin (alpha Rg) (beta Rg) =
    (borelPlane h e hz hk u).map (embedM Rg) at hbaseJ
  rw [hfix,hbaseJ] at hJ
  refine ⟨act Rg f (beta Rg),?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff Rg f (alpha Rg) (beta Rg)).mpr
      (base_adjacent Rg)
  · have hh := congrArg (Subgroup.map (embedM Rg)) hgen
    rw [Subgroup.map_sup,hmapA,←MonoidHom.range_eq_map] at hh
    rw [hJ]
    change _ = stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    have hmapR : (F₀.map (embedM Rg)).map (MulAut.conj f⁻¹).toMonoidHom =
        (F₀.map (MulAut.conj g).toMonoidHom).map (embedM Rg) := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro x
      change f⁻¹*embedM Rg x*(f⁻¹)⁻¹=embedM Rg (g*x*g⁻¹)
      simp only [f,inv_inv,map_mul,map_inv]
    rw [hmapR]
    exact hh

include h e hz hk in
/-- For a large image on either cover, an adjusted full seed generates with
an actual Borel edge and normalizes the entire backward critical kernel
joined to the initial seed. The same residual transporter realizes both
selected vertices; the actor retains the full central attachment. -/
theorem borel_four_large_adjusted_backward_selection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ Z Rg z ∧ Z Rg (p.walk.getVert 3) ≤ A ∧
      A.relIndex (Z Rg z) ≤ 2 ∧
      ⁅Z Rg (alpha Rg),A⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ ∧
      ∃ d t, ∃ x ∈ Ltilde Rg (alpha Rg),
        act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
        Adjacent Rg (alpha Rg) t ∧ Adjacent Rg d t ∧
        edgeOffenderJoin (alpha Rg) t ⊔ A = stabilizer Rg (alpha Rg) ∧
        (Z Rg (p.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
        Q Rg t ⊔ A = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg) ∧
          A ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg (alpha Rg) :
              Subgroup (FreeAmalgam Rg)) : Set _) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨A,hAZ,hattach,hindex,hpres,hcontrol,a,ha,ha2,heven⟩ :=
    large_critical_adjusted_seed h e hz hk p hp
  have hZG : Z Rg z ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl (sourceDistance_pos h) p.critical
  have hAG := hAZ.trans hZG
  obtain ⟨t,hat,hJgen⟩ := borel_even_actor_generating_mover h e hz hk u hR A hAG a ha ha2 heven
  have hJT := (remaining_edge_thompson h e hz hk u (Or.inr hR) rfl hat).2.2.1
  have htG : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hv => hv.2 _ (adjacent_symm Rg hat)
  have hgen : Q Rg t ⊔ A = stabilizer Rg (alpha Rg) := by
    apply le_antisymm (sup_le htG hAG)
    rw [←hJgen]
    exact sup_le_sup hJT le_rfl
  have hgenZ : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) :=
    le_antisymm (sup_le (le_sup_left.trans hgen.le) hZG)
      (hgen.symm.le.trans (sup_le_sup_left hAZ _))
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have htwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg z)).to_le hAZ
  have hAn : ¬ A ≤ Q Rg (alpha Rg) := by
    intro hn
    have hcom : A.comap (embedM Rg) ≤ pCore 2 M := by
      have hh := comap_mono (f := embedM Rg) hn
      rwa [Q_alpha_comap Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
    have hm : (A.comap (embedM Rg)).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [CubicAction.projection_kernel h e hz hk]
      exact hcom.trans le_sup_right
    have ha1 : a = 1 := mem_bot.mp (hm ▸ ha)
    rw [ha1,orderOf_one] at ha2
    contradiction
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hbc : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hab
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hzQb : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant _ p.end_color]
    change p.walk.length-1 < sourceDistance h
    omega
  have hfixed : Z Rg (p.walk.getVert 1) ⊓ centralizer
      (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hJgen]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans
        ((terminal_edge_seed_central hbc).trans (centralizer_le (hAZ.trans hzQb)))))
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) hab hat
  obtain ⟨x,hx,_,_,_,hxt,hxv⟩ := residual_star_transporter h rfl hab g hg
  have hxt' : act Rg x (p.walk.getVert 1) = t := hxt.trans hgt
  let d := act Rg x (p.walk.getVert 2)
  have hdt : Adjacent Rg d t := by
    rw [←hxt']
    exact (adjacent_act_iff Rg x _ _).mpr hcb
  have hd : color Rg d = false := by
    rw [action_preserves_color]
    exact (p.vertex_color (by omega)).mpr (by decide)
  have hxG := Ltilde_le_stabilizer (alpha Rg) hx
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hxG))
  have hel := large_critical_four_forward_eligible h e hz hk hb p hp
  have hdout : ¬ U Rg d ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hn
    apply hel
    change U Rg (act Rg x (p.walk.getVert 2)) ≤ _ at hn
    rw [U_act,←hB] at hn
    exact (map_le_map_iff_of_injective (MulAut.conj x⁻¹).injective).mp hn
  have hescape : ¬ Z Rg d ≤ Q Rg (p.walk.getVert 2) := by
    intro hn
    apply hdout
    have hprev : Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
      simpa only [hl,Nat.reduceSub] using hn
    exact (DistanceEight.U_le_Z Rg d).trans
      (controlled_backward_kernel_le_slice h e hz hb2 p A hAG htwo hAn hcontrol hat hdt
        hgen (Z Rg d) le_rfl hprev ((show Q Rg t ≤ stabilizer Rg d from
          fun _ hv => hv.2 _ (adjacent_symm Rg hdt)).trans (Z_normalized Rg d)))
  obtain ⟨q,hqt,hover⟩ := four_prepend_selected h hb p hd hat hdt hescape
  have hbound : ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg) := by
    have hh := (commutator_mono
      (inf_le_inf_right (Q Rg (p.walk.getVert (p.walk.length-2)))
        (terminal_neighbor_seed_radius hat hdt)) le_rfl).trans hcontrol
    simpa only [hl,Nat.reduceSub] using hh
  have hnorm : A ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg (alpha Rg) :
        Subgroup (FreeAmalgam Rg)) : Set _) :=
    normalize_join_of_commutator _ _ _ (hAG.trans (Z_normalized Rg _)) hbound
  refine ⟨A,hAZ,?_,hindex,hpres,d,t,x,hx,rfl,hxt',hat,hdt,hJgen,hfixed,hgen,hgenZ,q,hqt,hover,hbound,hnorm⟩
  simpa only [hl,Nat.reduceSub] using hattach

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
