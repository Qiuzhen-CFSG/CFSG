module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignmentControl
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CriticalEscape

/-!
# Excluding trapped radii in the original nonsylow replacement

The three-pair alignment/control theorem is transported from the moved
cover to the full endpoint seed. Its last-edge attachment centralizes
both actors, so adjoining that attachment preserves their commutators.
The full critical kernel is identified with the fixed subgroup of the
original critical seed. If control holds, its displacement and the
original critical line force normalization of the selected join, contrary
to the retained selector. Thus alignment is forced with the original
critical commutator times the actual endpoint center.

Apply this to the same line, cubic, neighbor transporter, path orientation
and residual rotation supplied by CubeAlignment. That line was proved
unaligned, giving the contradiction to a trapped radius. Both the
order-sixteen and order-thirty-two covers and all central attachments
remain present; the original MS2(a) radical is only assumed nonsylow.

Transport gives radius escape at every component vertex and the universal
critical-escape premise on the actual graph. The consumer applications
produce overlapping backward and forward critical paths and both forward
slice lower bounds, without a strict-slice or point-core-image premise.
The source (5.9) strict bound, terminal arguments, original Sylow branch
and distance-four exclusions remain separate obligations.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3), (5.7)--(5.8), printed pp.866--867,919--920. The line R in
R Z(G_alpha') is the original critical commutator, not the MS2(a) radical.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


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

private theorem map_center_eq_range_inf_centralizer {M N : Type*} [Group M] [Group N]
    (i : M →* N) (hi : Function.Injective i) :
    (center M).map i = i.range ⊓ centralizer (i.range : Set N) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    refine ⟨⟨x,rfl⟩,?_⟩
    rintro y ⟨z,rfl⟩
    simpa only [←map_mul] using congrArg i ((mem_center_iff.mp hx) z)
  · rintro x ⟨⟨y,rfl⟩,hc⟩
    refine ⟨y,mem_center_iff.mpr ?_,rfl⟩
    intro z
    apply hi
    simpa only [map_mul] using hc (i z) ⟨z,rfl⟩

include s in
/-- Alignment/control on a full endpoint seed. The central edge attachment
is retained and shown to centralize both actual actors. -/
theorem cube_edge_alignment_or_control (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {c t : Vertex d.radical} (hcol : color d.radical c = false)
    (hct : Adjacent d.radical c t)
    (A P : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ Q d.radical t) (hP : P ≤ Q d.radical t)
    (hne : ¬ A ≤ Q d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ ≤
      ⁅Z d.radical c,A⁆ ⊔
        (stabilizer d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))) ∨
    ⁅Z d.radical c,P⁆ ≤
      ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ ⊔ ⁅Z d.radical c,A⁆ := by
  have hcoords : ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical c ∧
      d.radical.map i = Q d.radical t ∧ (pCore 2 d.overgroup).map i = Q d.radical c ∧
      (replacementMoved d).map i = U d.radical c := by
    obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical c t).mp hct
    · rcases hg with ⟨rfl,rfl⟩
      let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
      refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_,?_,?_⟩
      · have he := stabilizer_act d.radical g (alpha d.radical)
        simpa only [i,alpha,act_mVertex,one_mul,stabilizer_m_base,Mbar,MonoidHom.range_comp] using he.symm
      · have he := Q_act d.radical g (beta d.radical)
        rw [Q_beta] at he
        simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
      · have he := Q_act d.radical g (alpha d.radical)
        rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
      · have he := U_act d.radical g (alpha d.radical)
        rw [hc.U_eq_moved] at he
        simpa only [alpha,act_mVertex,one_mul,map_map] using he.symm
    · rw [hg.1] at hcol
      cases hcol
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := hcoords
  have hmA : (A.comap i).map i = A :=
    map_comap_eq_self (hA.trans (hiR ▸ map_le_range i _))
  have hmP : (P.comap i).map i = P :=
    map_comap_eq_self (hP.trans (hiR ▸ map_le_range i _))
  have hAr : A.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hPr : P.comap i ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmP,hiR]
  have hAn : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    apply hne
    have hm := map_mono (f := i) hh
    rwa [hmA,hiQ] at hm
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hh := cube_cover_alignment_or_control s u hR (A.comap i) (P.comap i) hAr hPr hAn hidx
  have hmF : (replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup)).map i =
      U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)) := by
    rw [←map_inf_centralizer_of_injective i hi,hiU,hmA]
  have hmC : (replacementMoved d ⊓ center d.overgroup).map i ≤
      stabilizer d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := i) (show replacementMoved d ⊓ center d.overgroup ≤ center d.overgroup from inf_le_right)
    rwa [map_center_eq_range_inf_centralizer i hi,hir] at hh
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [hcol] at hh
    cases he : color d.radical t <;> simp_all
  have hseed : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [Z,if_neg (by simp [ht])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hseedA := hseed.trans (centralizer_le hA)
  have hseedP := hseed.trans (centralizer_le hP)
  have hseedN : Z d.radical t ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical hcol hct).trans (Z_le_stabilizer d.radical c)).trans (U_normalized c)
  let F := U d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical))
  have heq : Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)) = F ⊔ Z d.radical t := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct,
      sup_comm (U d.radical c),inf_centralizer_sup_of_centralizing _ _ _ hseedN hseedA]
    exact sup_comm _ _
  have hF : ⁅Z d.radical c ⊓ centralizer (A : Set (FreeAmalgam d.radical)),P⁆ = ⁅F,P⁆ := by
    rw [heq]
    exact commutator_sup_fixed F (Z d.radical t) P
      ((le_inf hseedN (hseedA.trans (centralizer (A : Set (FreeAmalgam d.radical))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf) hseedP
  have hZA : ⁅Z d.radical c,A⁆ = ⁅U d.radical c,A⁆ := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    exact commutator_sup_fixed _ _ _ hseedN hseedA
  have hZP : ⁅Z d.radical c,P⁆ = ⁅U d.radical c,P⁆ := by
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d hcol hct]
    exact commutator_sup_fixed _ _ _ hseedN hseedP
  rcases hh with hh | hh
  · left
    have hm := map_mono (f := i) hh
    rw [Subgroup.map_sup,map_commutator,map_commutator,hmF,hiU,hmA,hmP] at hm
    rw [hF,hZA]
    exact hm.trans (sup_le_sup_left hmC _)
  · right
    have hm := map_mono (f := i) hh
    rw [Subgroup.map_sup,map_commutator,map_commutator,map_commutator,hmF,hiU,hmA,hmP] at hm
    rwa [hZP,hF,hZA]

include s in
/-- The selected nonnormalization excludes control, forcing alignment of the
full reverse-kernel commutator with the original critical line and endpoint center. -/
theorem cube_critical_kernel_alignment
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (P : Subgroup (FreeAmalgam d.radical))
    (hP : P ≤ Q d.radical (p.walk.getVert (p.walk.length-1)))
    (hHP : ⁅Z d.radical z ⊓ Q d.radical a,P⁆ ≤ P)
    (hnorm : ¬ Z d.radical z ≤ normalizer
      ((P ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical z ⊓ Q d.radical a,P⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
      (stabilizer d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hzt : Adjacent d.radical z t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hA : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : Z d.radical z ⊓ Q d.radical a =
      Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical z)) (inclusion_injective _)
  have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ 2 :=
    ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical z) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hh := cube_edge_alignment_or_control s hc u hR p.end_color hzt
    (Z d.radical a) P hA hP p.critical.2 hindex
  rw [←hfixed,commutator_comm (Z d.radical z) (Z d.radical a)] at hh
  rcases hh with ha | hcontrol
  · exact ha
  · exfalso
    apply hnorm
    have hline : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical a)
    apply le_normalizer_iff_commutator_le_left.mpr
    apply commutator_sup_le_of_relative_normal (P ⊔ Z d.radical a)
      P (Z d.radical a) (Z d.radical z) (P ⊔ Z d.radical a)
      (P ⊔ Z d.radical a).le_normalizer le_sup_left le_sup_right
    · rw [commutator_comm]
      exact hcontrol.trans (sup_le (hHP.trans le_sup_left) (hline.trans le_sup_right))
    · exact hline.trans le_sup_right

include e hz hn in
/-- Source (5.8)'s radius obstruction is impossible for the actual nonsylow
replacement, with no strict slice or full point-core assumption. -/
theorem nonsylow_radius_escape_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ¬ V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  intro htrapped
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨delta,hdelta,hel,t,hat,g,hg,hgt,hct,x,hx,hxN,hx3,hgen,z,q,hq,hnorm,
    hcard,hseed,hedge,hmiddle,hcent,hncent,hpre,k,hk,hkt,r,hrt,hover,hi,hj,hK,hZ,hU,hunalign⟩ :=
      nonsylow_trapped_radius_rotated_unaligned_line_knownSimple
        (e := e) (hz := hz) (hn := hn) hb4 hns p htrapped
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hu]
  have hp := nonsylow_trapped_radius_predecessor_kernels_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p htrapped q
  have hsmall : (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [hp.2.1]
    decide
  have hVq : V d.radical (alpha d.radical) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) := by
    have hlen : q.walk.length=p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    rcases hq with ⟨hz,hverts⟩ | ⟨hz,hverts⟩
    · rw [hlen,hverts]
      exact htrapped
    · rw [hlen,hverts,Q_act]
      have hV : (V d.radical (alpha d.radical)).map (MulAut.conj x⁻¹).toMonoidHom =
          V d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical _
          ((stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx)))
      rw [←hV]
      exact map_mono htrapped
  have hdist : (cosetGraph d.radical).dist (act d.radical g delta) (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist (act d.radical g delta) t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical)=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := act d.radical g delta) (v := t) (w := alpha d.radical)
  have hD : Z d.radical (act d.radical g delta) ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hVq
  have hl : 2 < q.walk.length := q.length_eq_b ▸ hb
  have het : Adjacent d.radical z (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-1) (by omega)
    rw [show q.walk.length-1+1=q.walk.length by omega,q.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hlast : color d.radical (q.walk.getVert (q.walk.length-1))=true := by
    have hh := adjacent_color_ne d.radical het
    rw [q.end_color] at hh
    cases he : color d.radical (q.walk.getVert (q.walk.length-1)) <;> simp_all
  have hpred : Adjacent d.radical (q.walk.getVert (q.walk.length-2))
      (q.walk.getVert (q.walk.length-1)) := by
    have hh := q.walk.adj_getVert_succ (i := q.walk.length-2) (by omega)
    rw [show q.walk.length-2+1=q.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  exact hunalign (cube_critical_kernel_alignment s hc hb u hR q hsmall
    (Z d.radical (act d.radical g delta))
    (hD.trans (Q_le_adjacent_h d.radical hlast hpred))
    (hseed.trans inf_le_left) hnorm)

include e hz hn in
/-- Radius escape at every component vertex of the original natural graph. -/
theorem nonsylow_radius_escape_at_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ V d.radical a ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := nonsylow_radius_escape_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns (a' := act d.radical j⁻¹ a')
  rw [←hbase] at base
  intro htrapped
  apply base (p.act j⁻¹)
  have hm := map_mono (f := (MulAut.conj j).toMonoidHom) htrapped
  simpa only [CriticalPath.act,actWalk_length,actWalk_getVert,V_act,Q_act,inv_inv] using hm

include e hz hn in
/-- Universal critical escape in the actual nonsylow replacement graph,
including every shortest predecessor of every critical pair. -/
theorem nonsylow_criticalEscape_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    Factorization.CriticalEscape d.radical (replacementGeometry h d) := by
  intro a ha a' hcrit c hce hpath
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist a c
  obtain ⟨v,hv⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a'
  let p : CriticalPath d.radical (replacementGeometry h d) a a' :=
    ⟨ha,w.append v,by rw [SimpleGraph.Walk.length_append,hw,hv,hce,hpath],hcrit⟩
  have heq : p.walk.getVert (p.walk.length-2) = c := by
    change (w.append v).getVert ((w.append v).length-2) = c
    rw [SimpleGraph.Walk.length_append,hv,hce,Nat.add_sub_cancel]
    simp only [SimpleGraph.Walk.getVert_append,lt_self_iff_false,ite_false,
      Nat.sub_self,SimpleGraph.Walk.getVert_zero]
  simpa only [heq] using nonsylow_radius_escape_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hns p

include e hz hn in
/-- Both source (5.8) slice lower bounds and the actual forward shift follow
without a point-core-image or strict-slice hypothesis. -/
theorem nonsylow_forward_path_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2)) ∧
      2 ≤ (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical a) ∧
      ∃ z, ∃ q : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) z,
        (cosetGraph d.radical).dist a' z = 2 ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) ∧
        q.walk.getVert (q.walk.length-2) = a' := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hesc := nonsylow_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb4 hns
  exact ⟨critical_forward_slice_index_two_le_of_escape s hc hb hesc p,
    critical_start_slice_index_two_le s hc hb p,
    critical_forward_extension_of_escape s hc hb hesc p⟩

include e hz hn in
/-- An actual backward critical path follows from radius escape, with every
overlapping vertex retained and no strict Baumann-slice premise. -/
theorem nonsylow_backward_path_of_radius_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ c t, Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
        (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1=t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2)=p.walk.getVert i) ∧
        2 ≤ (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) := by
  have hb : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hd : (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-2)) + 2 =
      (replacementGeometry h d).b d.radical := by
    rw [p.dist_start (Nat.sub_le _ _),p.length_eq_b]
    change replacementDistance h d - 2 + 2 = replacementDistance h d
    omega
  obtain ⟨c,hcol,hca,hcrit⟩ := exists_critical_shift d.radical p.start_color hd
    (nonsylow_radius_escape_at_knownSimple (e := e) (hz := hz) (hn := hn) hb4 hns p)
  obtain ⟨w,hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist c a
  have hwlen : w.length=2 := hw.trans hca
  let t := w.getVert 1
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      w.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := by
    apply adjacent_symm d.radical
    apply (cosetGraph_adj d.radical _ _).mp
    have hh := w.adj_getVert_succ (i := 1) (by omega)
    simpa only [show 1+1=w.length by omega,SimpleGraph.Walk.getVert_length] using hh
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hwlen hcrit.2
  have hqt : q.walk.getVert 1=t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hwlen,show 1<2 from by decide,ite_true,t]
  have hover (i : ℕ) (hi : i ≤ p.walk.length-2) :
      q.walk.getVert (i+2)=p.walk.getVert i := p.prepend_two_overlap _ _ _ _ _ hi
  have hqa : q.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  refine ⟨c,t,hat,hct,q,hqt,hover,?_⟩
  have hh := critical_start_slice_index_two_le s hc hb q
  rwa [hqa] at hh


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
