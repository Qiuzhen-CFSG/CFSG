module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OmegaExtension
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedSmallRadical
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedElementary
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.SixteenEqual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedSixteenUnequal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.FullSeedBackward
/-!
# Residual fixedness of the full radius at a large distance-four path

A large critical path supplies one restricted endpoint seed that retains its
edge attachment, its critical movement and an even involution in the literal
symmetric quotient. The existing cube-generation calculation lets us choose
an incident edge whose small mover and that same seed generate the entire
starting stabilizer. The controlled backward selector retains this edge and
agrees on its whole kernel, so the reciprocal quadratic-core calculation
applies without replacing the graph or any central attachment.

If the selected edge movers differ, their index-four intersection makes the
whole midpoint movement equal the critical commutator and hence residual-fixed.
If they coincide, the common quadratic mover centralizes that commutator;
the selected endpoint seed also centralizes it, and together they generate
the whole midpoint stabilizer. In both cases the hatted backward seed has
index at most two and a strict Baumann slice, so its normal span captures the
full radius.

This closes the order-sixteen radical-image branch on both moving covers.
Combining it with the smaller and elementary radical images gives full-radius
residual fixedness with only the original large critical path and b = 4.
The original radical, literal projection and Sylow status remain unchanged.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2), (5.5), (5.12)(2), printed pp.867,914--917,925.
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


open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
local notation "S" => Equiv.Perm (Fin 6)

include s in
private theorem sixteen_small_mover_generating_neighbor
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWG : W ≤ stabilizer d.radical (alpha d.radical))
    (a : S) (ha : a ∈ (W.comap (embedM d.radical)).map s.projection)
    (hao : orderOf a = 2) (haeven : a ∈ alternatingGroup (Fin 6)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical t) 4 ⊔ W = stabilizer d.radical (alpha d.radical) := by
  let J := SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4
  have hnormal := SylowLarge.sixteen_radical_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard
  obtain ⟨u,_,_,hJ,hJi,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) (SixteenUnequal.sixteen_nonelementary hcard) hb
  rw [hnormal] at hJ hJi
  have hJimage : J.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    have hproj : s.projection = (fullSymmetricAction_knownSimple h e hz hn d hb).projection :=
      (SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s).trans
        (SourceReduction.fullSymmetricAction_projection_unique h e hz hn d
          (fullSymmetricAction_knownSimple h e hz hn d hb)).symm
    rw [hproj,show J = _ from hJ]
    exact hJi
  obtain ⟨v₀,hv⟩ := CubeGeneration.even_generator ⟨a,haeven⟩
    ((Subgroup.orderOf_coe ⟨a,haeven⟩).symm.trans hao)
  let v : S := v₀.val
  let w := v*u⁻¹
  obtain ⟨g,hgw⟩ := s.surjective w
  let Jg := J.map (MulAut.conj g).toMonoidHom
  have hJgimage : Jg.map s.projection = (D 6).map (MulAut.conj v).toMonoidHom := by
    have he : s.projection.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj w).toMonoidHom.comp s.projection := by
      apply MonoidHom.ext
      intro x
      change s.projection (g*x*g⁻¹) = w*s.projection x*w⁻¹
      rw [map_mul,map_mul,map_inv,hgw]
    rw [show Jg = _ from rfl,map_map,he,←map_map,hJimage,CubeCommonFixer.conjugate_twice]
    simp only [w,mul_assoc,inv_mul_cancel,mul_one]
  have hQ : (pCore 2 d.overgroup).map (MulAut.conj g).toMonoidHom = pCore 2 d.overgroup :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hU : (replacementMoved d).map (MulAut.conj g).toMonoidHom = replacementMoved d := by
    let := replacementMoved_normal h d
    exact mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top g)
  have hQJ : pCore 2 d.overgroup ≤ J := by
    let := replacementMoved_normal h d
    apply SmallMover.kernel_le_join _ _ _ 4 (by decide) (replacement_core_le_radical h d)
    rw [←moved_centralizer s]
    exact le_centralizer_iff.mpr le_rfl
  have hker : s.projection.ker ≤ Jg := by
    rw [s.projection_kernel,←hQ]
    exact map_mono hQJ
  let A := W.comap (embedM d.radical)
  have hgen : Jg ⊔ A = ⊤ := by
    apply map_injective_of_ker_le s.projection (hker.trans le_sup_left) le_top
    rw [Subgroup.map_sup,hJgimage,map_top_of_surjective s.projection s.surjective]
    apply top_unique
    rw [←hv]
    exact sup_le_sup_left (zpowers_le.mpr ha) _
  let f := (embedM d.radical g)⁻¹
  let t := act d.radical f (beta d.radical)
  have hf : f ∈ stabilizer d.radical (alpha d.radical) := by
    change f ∈ stabilizer d.radical (mVertex d.radical 1)
    rw [stabilizer_m_base]
    exact ⟨g⁻¹,by simp only [map_inv,f]⟩
  have ht : Q d.radical t = (d.radical.map (MulAut.conj g).toMonoidHom).map (embedM d.radical) := by
    rw [Q_act,Q_beta,SylowCompatible.image_conjugate]
    simp only [f,inv_inv]
  have hJmap : Jg.map (embedM d.radical) =
      SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
        (Q d.radical t) 4 := by
    change ((SmallMover.join (replacementMoved d) (pCore 2 d.overgroup) d.radical 4).map
      (MulAut.conj g).toMonoidHom).map (embedM d.radical) = _
    rw [SmallMover.join_map _ (MulAut.conj g).injective,hU,hQ,
      SmallMover.join_map _ (embedM_injective d.radical),←hc.U_eq_moved,
      ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←ht]
  refine ⟨t,?_,?_⟩
  · have hfix : act d.radical f (alpha d.radical) = alpha d.radical := hf
    rw [←hfix]
    exact (adjacent_act_iff d.radical f _ _).mpr (base_adjacent d.radical)
  · have hmapA : A.map (embedM d.radical) = W :=
      map_comap_eq_self (hWG.trans_eq (stabilizer_m_base d.radical))
    have hh := congrArg (Subgroup.map (embedM d.radical)) hgen
    rw [Subgroup.map_sup,hJmap,hmapA,←MonoidHom.range_eq_map] at hh
    exact hh.trans (stabilizer_m_base d.radical).symm

include e hz hn in
/-- The order-sixteen image branch of full-radius residual fixedness. A cube
small mover and the same controlled even endpoint actor generate the whole
stabilizer; unequal movers reduce to the reciprocal core-product calculation. -/
theorem sixteen_large_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hindex,hcritical,hexact,a,ha,hao,haeven⟩ :=
    large_image_full_seed_even_control s hc hb p hlarge
  have hWG₀ : W ≤ stabilizer d.radical (alpha d.radical) := hWZ.trans
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
      (replacementDistance_pos h d) p.critical)
  have hWne : ¬ W ≤ Q d.radical (alpha d.radical) := by
    intro hWQ
    have hker : W.comap (embedM d.radical) ≤ s.projection.ker := by
      rw [s.projection_kernel]
      have hh := comap_mono (f := embedM d.radical) hWQ
      rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
        (replacement_core_le_radical h d)] at hh
    have he := (Subgroup.map_eq_bot_iff (W.comap (embedM d.radical))).mpr hker
    have ha1 : a = 1 := mem_bot.mp (he ▸ ha)
    rw [ha1,orderOf_one] at hao
    omega
  obtain ⟨t,hat,hgenJ⟩ := sixteen_small_mover_generating_neighbor s hc hb2 hcard W hWG₀ a ha hao haeven
  have hTG : Q d.radical t ≤ stabilizer d.radical (alpha d.radical) :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hgenQ : Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) :=
    le_antisymm (sup_le hTG hWG₀) (hgenJ.ge.trans
      (sup_le_sup_right (SmallMover.join_le _ _ _ _) W))
  have hgen : (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) := by
    rw [SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard rfl hat]
    exact hgenQ
  have hRZ : ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ ≤ Z d.radical (alpha d.radical) :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical _)
  have hbound' := hexact.le.trans hRZ
  have hbound : ⁅V d.radical (alpha d.radical) ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤ Z d.radical (alpha d.radical) := by
    simpa only [hl,show 4-2=2 from rfl] using hbound'
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) := le_sup_right.trans_eq hgen
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hd1 : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) := by
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  have hct : Adjacent d.radical (act d.radical x (p.walk.getVert 2)) t := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hd1
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  have hi : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical x (p.walk.getVert 2))) =
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) := by
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective,hB]
  have hstrict := large_image_forward_slice_gt_two_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hel : ¬ U d.radical (act d.radical x (p.walk.getVert 2)) ≤
      B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    have he := relIndex_eq_one.mpr hh
    rw [hi] at he
    omega
  obtain ⟨k,hk,g,hg,hagree,q,hq1,hover,hidx⟩ := SylowActor.relative_controlled_backward_shift
    s hb2 p W hWG hWne hbound hat hct hgen hel
  have hc't : Adjacent d.radical (act d.radical k (act d.radical x (p.walk.getVert 2))) t := by
    have hfix : act d.radical k t = t := hk
    simpa only [hfix] using (adjacent_act_iff d.radical k _ t).mpr hct
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by omega)
  have hidx' := hidx.trans hi
  have hstrict' : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical k (act d.radical x (p.walk.getVert 2)))) := by
    rw [hidx']
    exact hstrict
  have hout : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical k (act d.radical x (p.walk.getVert 2))) (p.walk.getVert 2),
      q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
      q'.walk.getVert 3 = p.walk.getVert 1 := by
    have hex : ∃ q' : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical k (act d.radical x (p.walk.getVert 2))) (p.walk.getVert (p.walk.length-2)),
        q'.walk.getVert 1 = t ∧ q'.walk.getVert 2 = alpha d.radical ∧
        q'.walk.getVert 3 = p.walk.getVert 1 := ⟨q,hq1,hq2,hq3⟩
    have he : p.walk.length-2 = 2 := by omega
    rw [he] at hex
    exact hex
  obtain ⟨q',hq1',hq2',hq3'⟩ := hout
  let c := act d.radical k (act d.radical x (p.walk.getVert 2))
  let K := Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)
  let D := K ⊔ Z d.radical (alpha d.radical)
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hc't)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hKV : K ≤ V d.radical (alpha d.radical) :=
    inf_le_left.trans ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
  have hmove : ⁅K,W⁆ ≤ ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans_eq hexact
  have hZaY : Z d.radical (alpha d.radical) ≤
      V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert 2) := by
    apply le_inf (Z_le_VBall d.radical _ 2)
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ rfl)
    rw [(replacementGeometry h d).distance_constant _ rfl,p.dist_start (by omega)]
    exact hb2
  have hDexact : ⁅D,W⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :=
    le_antisymm ((commutator_mono (sup_le (le_inf hKV inf_le_right) hZaY) le_rfl).trans_eq hexact)
      (hcritical.ge.trans (commutator_mono le_sup_right le_rfl))
  have hDmove : ⁅D,W⁆ ≤ Z d.radical (alpha d.radical) := hDexact.le.trans hRZ
  have hWD : W ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hDmove.trans le_sup_right)
  have hcent : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (W : Set (FreeAmalgam d.radical)) := by
    have hpre : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤ Z d.radical (p.walk.getVert 2) :=
      ((critical_Z_commutator_le_moving (h := h) q').trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical _)
    have hQ : Z d.radical (p.walk.getVert 2) ≤ Q d.radical a' := by
      apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ q'.end_color)
      rw [(replacementGeometry h d).distance_constant _ q'.end_color,p.dist_end]
      change p.walk.length-2 < replacementDistance h d
      omega
    have hCZ : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color))
    exact (hpre.trans (hQ.trans hCZ)).trans
      (centralizer_le hWZ)
  have hback : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) := by
    by_contra! hsmall
    apply strict_small_actor_false s hc hb q' hsmall W
    · simpa only [hq1',hq2'] using hgenQ
    · simpa only [hq2'] using hstrict'
    · simpa only [hq2'] using hWne
    · rw [hq2']
      exact hDmove
    · exact hcent
  by_contra hnot
  have hequal := sixteen_selected_backward_movers_eq_of_radius_not_fixed_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hlarge W q' hq1' hq2' hback hstrict' hgenQ hcent
    ⟨x,hx,hxt,k,hk,rfl,g,hg,hagree⟩ hnot
  let J := SmallMover.join (U d.radical (alpha d.radical)) (Q d.radical (alpha d.radical))
    (Q d.radical t) 4
  let R₀ := ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆
  have hqzQ : Z d.radical (p.walk.getVert 2) ≤ Q d.radical (alpha d.radical) := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ q'.end_color)
    rw [(replacementGeometry h d).distance_constant _ q'.end_color,SimpleGraph.dist_comm,
      p.dist_start (by omega)]
    exact hb2
  have hQaJ : Q d.radical (alpha d.radical) ≤ J :=
    (SixteenUnequal.sixteen_edge_small_mover_knownSimple
      (e := e) (hz := hz) (hn := hn) hb2 hcard rfl hat).1
  have hquad := SixteenEqual.small_mover_full_seed_quadratic
    (e := e) (hz := hz) (hn := hn) hb2 hcard q'.start_color hc't
  dsimp only at hquad
  rw [hequal] at hquad
  have hRJ : R₀ ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (commutator_mono le_rfl (hqzQ.trans hQaJ)).trans
      (commutator_eq_bot_iff_le_centralizer.mp hquad)
  have hRG : R₀ ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hgenJ]
    exact sup_le (le_centralizer_iff.mp hRJ) (le_centralizer_iff.mp hcent)
  have hdata := large_midpoint_movement s hc hb q' hback
  have hRX : R₀ ≤ X d.radical (alpha d.radical) := by
    rw [←hq2']
    exact hdata.2.2.2.trans hdata.2.1
  have hfixed : R₀ ≤ fixedCore d.radical (alpha d.radical) :=
    le_inf (hRX.trans (omegaCenter_le _)) (hRG.trans (centralizer_le (Ltilde_le_stabilizer _)))
  exact hnot (large_backward_critical_fixed_radius s hc hb p hlarge q' hq2' hback hstrict' hfixed)

include e hz hn in
/-- A large critical path at distance four has residual-fixed full-radius
core movement, for every actual radical image and both moving covers. -/
theorem large_radius_core_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical) := by
  let A := d.radical.map (SourceReduction.projection h e hz hn d)
  by_cases hsmall : Nat.card A ≤ 4
  · exact small_radical_large_radius_core_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) hb (Or.inl hsmall) p hlarge
  by_cases height : Nat.card A = 8
  · by_cases hel : IsElementaryAbelian 2 A
    · exact elementary_radical_large_radius_core_fixed_knownSimple
        (e := e) (hz := hz) (hn := hn) hb hel p hlarge
    · exact small_radical_large_radius_core_fixed_knownSimple
        (e := e) (hz := hz) (hn := hn) hb (Or.inr ⟨height,hel⟩) p hlarge
  apply sixteen_large_radius_core_fixed_knownSimple (e := e) (hz := hz) (hn := hn) hb _ p hlarge
  change Nat.card A = 16
  have hp : IsPGroup 2 A := (replacement_radical_isPGroup h d).map _
  obtain ⟨P,hAP⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
  have hPcard : Nat.card (P : Subgroup S) = 16 := by
    have hh := congrArg (fun P : Sylow 2 S => Nat.card (P : Subgroup S)) hg
    change Nat.card ((P : Subgroup S).map (MulAut.conj g).toMonoidHom) = Nat.card sylowCarrier at hh
    rwa [card_map_of_injective (MulAut.conj g).injective,card_sylowCarrier] at hh
  have hu : Nat.card A ≤ 16 := (card_le_of_le hAP).trans_eq hPcard
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn4 : n ≤ 4 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [hn] using hu
  have hvals : Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 4 ∨
      Nat.card A = 8 ∨ Nat.card A = 16 := by
    rw [hn]
    interval_cases n <;> norm_num
  omega

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
