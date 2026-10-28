module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedSmallRadical
public import Theory.GroupTheory.ConjugateSpanSylow
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane

/-!
# Hatted seeds and elementary-image residual fixedness

For a large critical path at distance four, restrict the starting moving
cover by the full-cover calculation and retain its entire incident edge
seed. The resulting hatted seed has index at most two on the moving cover,
and its commutator with the whole midpoint core equals the original
critical commutator. This is the restricted seed required by the source;
the equality need not hold for the full starting seed.

If the radical action image is elementary abelian, its derived subgroup
acts trivially on the seed, so the actual first edge normalizes the
critical commutator. The full backward selector supplies the other
normalizing actor. The small commutator is therefore residual-fixed.
The selected backward slice has index greater than two, so the hatted
seed still escapes the Baumann subgroup. The chief-factor alternative
makes its normal span capture the moving radius, and RadiusTransfer
extends the resulting fixedness to the original full radius.

This includes both elementary order-eight images on the order-thirty-two
cover, without changing the original radical, quotient map, central
attachments or Sylow status. The non-elementary order-sixteen radical
image remains a separate source comparison.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii)(1), (5.0), (5.12)(2), printed pp.867,912,925--926.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

omit [Finite G] in
private theorem abelian_action_preserves_movement {H : Type*} [Group H]
    (P V A : Subgroup H) (hPV : P ≤ normalizer (V : Set H)) (hAP : A ≤ P)
    (hcom : ⁅P,P⁆ ≤ centralizer (V : Set H)) :
    P ≤ normalizer ((⁅V,A⁆ : Subgroup H) : Set H) := by
  apply le_normalizer_closure_iff.mpr
  rintro g hg _ ⟨v,hv,a,ha,rfl⟩
  let f := MulAut.conj g
  have hfv : f v ∈ V := (mem_normalizer_iff.mp (hPV hg) v).mp hv
  have hga : ⁅g,a⁆ ∈ centralizer (V : Set H) :=
    hcom (commutator_mem_commutator hg (hAP ha))
  have hzero : ⁅f v,⁅g,a⁆⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hga (f v) hfv)
  have hmove : ⁅f v,a⁆ ∈ V :=
    le_normalizer_iff_commutator_le_left.mp (hAP.trans hPV)
      (commutator_mem_commutator hfv ha)
  change f ⁅v,a⁆ ∈ ⁅V,A⁆
  rw [map_commutatorElement,show f a = ⁅g,a⁆ * a from conj_eq_commutatorElement_mul,
    commutatorElement_mul_right_eq_mul_conj,hzero,one_mul,←hga _ hmove,mul_inv_cancel_right]
  exact commutator_mem_commutator hfv ha

include s in
private theorem elementary_radical_critical_normalized
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    (hel : IsElementaryAbelian 2 (d.radical.map s.projection))
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z) :
    Q d.radical (p.walk.getVert 1) ≤
      normalizer ((⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let t := p.walk.getVert 1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hct : Adjacent d.radical (p.walk.getVert 2) t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hZT : Z d.radical z ≤ Q d.radical t := by
    apply (show Z d.radical z ≤ Q d.radical (p.walk.getVert 2) from ?_).trans
      (Q_le_adjacent_h d.radical ht hct)
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,
      SimpleGraph.dist_comm,p.dist_end,hl]
    exact show 2 < replacementDistance h d by omega
  have hTG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc p.start_color hat
  let := hel
  have hder : ⁅d.radical,d.radical⁆ ≤ s.projection.ker := by
    apply (Subgroup.map_eq_bot_iff _).mp
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr hel.toIsMulCommutative)
  have hderU : ⁅d.radical,d.radical⁆ ≤ centralizer (replacementMoved d : Set d.overgroup) := by
    rw [s.projection_kernel,←moved_centralizer s] at hder
    exact hder
  have hTU : ⁅Q d.radical t,Q d.radical t⁆ ≤ centralizer (U d.radical a : Set _) := by
    rw [←hiR,←map_commutator,←hiU]
    rintro _ ⟨x,hx,rfl⟩ y ⟨v,hv,rfl⟩
    simpa only [←map_mul] using congrArg i (hderU hx v hv)
  have hTZ : ⁅Q d.radical t,Q d.radical t⁆ ≤ centralizer (Z d.radical a : Set _) := by
    apply le_centralizer_iff.mpr
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d p.start_color hat]
    refine sup_le (le_centralizer_iff.mp hTU) ?_
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y
      (le_normalizer_iff_commutator_le_left.mp (Q d.radical t).le_normalizer hy)
  exact abelian_action_preserves_movement (Q d.radical t) (Z d.radical a) (Z d.radical z)
    (hTG.trans (Z_normalized d.radical a)) hZT hTZ

include s in
/-- The full hatted seed retains the first-edge attachment and has index at
most two on the moving cover. Its whole midpoint-core movement is exactly
the original critical commutator, on either cover and every radical image. -/
theorem critical_hatted_seed_midpoint_control
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ∃ E : Subgroup (FreeAmalgam d.radical),
      Z d.radical (p.walk.getVert 1) ≤ E ∧ E ≤ Z d.radical a ∧
      (E ⊓ U d.radical a).relIndex (U d.radical a) ≤ 2 ∧
      ⁅E,Q d.radical (p.walk.getVert 2)⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let D := ⁅Z d.radical a,Z d.radical z⁆
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hQcT : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hTG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hAz : Z d.radical z ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hfull : ⁅U d.radical a,Z d.radical z⁆ = D :=
    (seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat _ (hAz.trans hQcT)).symm
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hA : Z d.radical z ≤ i.range := (hAz.trans (hQcT.trans hTG)).trans_eq hir.symm
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) z p.end_color
  have hDR : D ≤ Z d.radical z :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans (DistanceEight.U_le_Z d.radical _)
  have hAA : ⁅U d.radical a,Z d.radical z⁆ ≤ centralizer (Z d.radical z : Set _) :=
    (hfull.le.trans hDR).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hcard := reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge
  obtain ⟨W,hW,hiW,hpres,hcontrol⟩ := embedded_cover_restriction_preserving s i hi
    (Z d.radical z) hA (hiQ.symm ▸ hcard) (hiU.symm ▸ hAA)
  rw [hiU] at hW hiW hpres hcontrol
  have hDQ : D ≤ centralizer (Q d.radical c : Set _) :=
    (large_midpoint_movement s hc hb p hlarge).2.2.2.trans
      (large_midpoint_core_quadratic s hc hb p hlarge)
  have hWD : ⁅W,Q d.radical c⁆ = D := by
    apply le_antisymm
    · exact (hcontrol _ ((hQcT.trans hTG).trans_eq hir.symm) (hfull.le.trans hDQ)).trans_eq hfull
    · rw [←hfull,←hpres]
      exact commutator_mono le_rfl hAz
  let E := W ⊔ Z d.radical t
  have hFZ : Z d.radical t ≤ Z d.radical a := adjacent_Z_le d.radical p.start_color hat
  have hEZ : E ≤ Z d.radical a := sup_le (hW.trans (DistanceEight.U_le_Z d.radical _)) hFZ
  have hFQ : Z d.radical t ≤ centralizer (Q d.radical c : Set _) := by
    intro x hx y hy
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hQcT hy)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hDN : Z d.radical a ≤ normalizer (D : Set _) :=
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le
      (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)))).trans (Subgroup.centralizer_le_normalizer _)
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  refine ⟨E,le_sup_right,hEZ,
    (relIndex_le_of_le_left (le_inf (show W ≤ E from le_sup_left) hW) index_ne_zero_of_finite).trans hiW,?_⟩
  apply le_antisymm
  · exact commutator_sup_le_of_relative_normal (Z d.radical a) W (Z d.radical t)
      (Q d.radical c) D hDN (hW.trans (DistanceEight.U_le_Z d.radical _)) hFZ hWD.le
      ((commutator_eq_bot_iff_le_centralizer.mpr hFQ).le.trans bot_le)
  · change D ≤ ⁅E,Q d.radical c⁆
    rw [←hWD]
    exact commutator_mono le_sup_left le_rfl

include s in
private theorem large_restricted_span_captures_moving_radius
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (E : Subgroup (FreeAmalgam d.radical))
    (hEV : E ≤ V d.radical (alpha d.radical))
    (hEB : ¬ E ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    Vcirc d.radical (alpha d.radical) ≤
      conjugateSpanBy E (stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical (alpha d.radical) := by
  let P := conjugateSpanBy E (stabilizer d.radical (alpha d.radical))
  let Y := P.comap (embedM d.radical)
  have hb2 : 2 < replacementDistance h d := by omega
  have hPV : P ≤ V d.radical (alpha d.radical) :=
    conjugateSpanBy_le hEV (V_normalized _)
  have hPG : P ≤ stabilizer d.radical (alpha d.radical) :=
    hPV.trans ((replacementGeometry h d).V_local _ rfl hb2)
  have hPN := le_normalizer_conjugateSpanBy E (stabilizer d.radical (alpha d.radical))
  have hYm : Y.map (embedM d.radical) = P :=
    map_comap_eq_self (hPG.trans_eq (stabilizer_m_base d.radical))
  let : Y.Normal := ⟨by
    intro y hy g
    change embedM d.radical (g*y*g⁻¹) ∈ P
    rw [map_mul,map_mul,map_inv]
    have hg : embedM d.radical g ∈ stabilizer d.radical (alpha d.radical) := by
      rw [show alpha d.radical = mVertex d.radical 1 from rfl,stabilizer_m_base]
      exact ⟨g,rfl⟩
    exact (mem_normalizer_iff.mp (hPN hg) (embedM d.radical y)).mp hy⟩
  have hLm : (replacementComponent d).map (embedM d.radical) = Ltilde d.radical (alpha d.radical) := by
    rw [Ltilde_alpha,replacement_residual h d]
  have hZm : (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  rcases critical_radius_normal_subgroup_dichotomy s hc hb2 p hlarge Y (comap_mono hPV) with hf | hm
  · have hf' := map_mono (f := embedM d.radical) hf
    rw [map_commutator,hYm,hLm,hZm] at hf'
    have hPB : P ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
      intro v hv
      apply (mem_B_iff d.radical (alpha d.radical) _ ((replacementGeometry h d).V_local _ rfl hb2) v).mpr
      refine ⟨hPV hv,?_⟩
      intro l hl
      rw [commutator_comm] at hf'
      exact hf' (commutator_mem_commutator hl hv)
    exact (hEB ((le_conjugateSpanBy E _).trans hPB)).elim
  · have hm' := map_mono (f := embedM d.radical) hm
    rw [map_commutator,radius_comap_map (h := h) hb2,hLm,Subgroup.map_sup,hYm,hZm] at hm'
    exact hm'

include s in
/-- A restricted seed escaping the actual Baumann slice captures the moving
radius. If its midpoint-core movement is residual-fixed, the entire original
radius-core commutator is residual-fixed. -/
theorem restricted_seed_radius_core_fixed
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (E : Subgroup (FreeAmalgam d.radical))
    (hEV : E ≤ V d.radical (alpha d.radical))
    (hEB : ¬ E ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hfixed : ⁅E,Q d.radical (alpha d.radical)⁆ ≤ fixedCore d.radical (alpha d.radical)) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let a := alpha d.radical
  let P := conjugateSpanBy E (stabilizer d.radical a)
  let D := fixedCore d.radical a
  have hb2 : 2 < replacementDistance h d := by omega
  have hEG : E ≤ stabilizer d.radical a := hEV.trans ((replacementGeometry h d).V_local _ rfl hb2)
  have hDN : stabilizer d.radical a ≤ normalizer (D : Set _) := fixedCore_normalized d.radical a
  have hPD : ⁅P,Q d.radical a⁆ ≤ D := by
    dsimp only [P]
    rw [conjugateSpanBy_eq_iSup_conj]
    apply commutator_iSup_le_of_relative_normal (stabilizer d.radical a) _ _ _ hDN
    · intro g
      exact (map_mono hEG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        ((stabilizer d.radical a).le_normalizer g.property))
    · intro g
      have hh := map_mono (f := (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom) hfixed
      have hQ : (Q d.radical a).map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom =
          Q d.radical a := mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a g.property)
      have hD : D.map (MulAut.conj (g : FreeAmalgam d.radical)).toMonoidHom = D :=
        mem_normalizer_iff_map_conj_eq.mp (hDN g.property)
      change (⁅E,Q d.radical a⁆).map _ ≤ D.map _ at hh
      rwa [map_commutator,hQ,hD] at hh
  apply radius_core_fixed_of_moving_core_fixed s hb2
  have hm := large_restricted_span_captures_moving_radius s hc hb p hlarge E hEV hEB
  apply (commutator_mono hm le_rfl).trans
  exact commutator_sup_le_of_relative_normal (stabilizer d.radical a) _ _ _ D hDN
    (conjugateSpanBy_le_self hEG) (Z_le_stabilizer d.radical _) hPD
    ((Z_centralizes_Q d.radical a rfl).le.trans bot_le)

include e hz hn in
/-- Elementary radical images make the backward critical movement invariant
under its actual edge. The restricted seed retains the edge attachment and
still escapes the Baumann slice, so its span captures the moving radius. -/
theorem elementary_radical_large_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hel : IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  let D := ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆
  have hdata := large_midpoint_movement s hc hb q hback
  have hcard := large_midpoint_movement_card s hc hb q hback
  have hTN := elementary_radical_critical_normalized s hc hb
    (by rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]) q
  rw [hq1] at hTN
  have hGN : stabilizer d.radical (alpha d.radical) ≤ normalizer (D : Set _) := by
    rw [←hgenQ]
    exact sup_le hTN ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  let := finite_Z d.radical c
  let : Finite (⁅Z d.radical c,Q d.radical (q.walk.getVert 2)⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hdata.1.trans (DistanceEight.U_le_Z d.radical _))) (inclusion_injective _)
  have hDcard : Nat.card D ≤ 8 := (card_le_of_le hdata.2.2.2).trans hcard
  have hDX : D ≤ X d.radical (alpha d.radical) := by
    rw [←hq2]
    exact hdata.2.2.2.trans hdata.2.1
  have hDF : D ≤ fixedCore d.radical (alpha d.radical) :=
    small_core_residual_fixed_knownSimple (h := h) (e := e) rfl D
      (hDX.trans (omegaCenter_le _)) ((Ltilde_le_stabilizer _).trans hGN) hDcard
  obtain ⟨E,hFE,hEZ,hiE,hEQ⟩ := critical_hatted_seed_midpoint_control s hc hb q hback
  rw [hq1] at hFE
  rw [hq2] at hEQ
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hEV : E ≤ V d.radical (alpha d.radical) := hEZ.trans
    ((Z_le_localZSpan d.radical c _).trans (localZSpan_le_V d.radical (by
      rw [←hq2,q.dist_start (by omega)])))
  have hEB : ¬ E ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hbad
    let : Finite (U d.radical c) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
    have hh := (relIndex_le_of_le_left (inf_le_left.trans hbad)
      (L := U d.radical c) index_ne_zero_of_finite).trans hiE
    omega
  exact restricted_seed_radius_core_fixed s hc hb p hlarge E hEV hEB (hEQ.le.trans hDF)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
