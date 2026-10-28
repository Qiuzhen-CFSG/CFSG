module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowStrict
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeLargeExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedChain

/-!
# Critical images and paired paths for elementary Sylow replacements

The elementary replacement image above distance four is the full three-pair
subgroup of the actual symmetric quotient. The existing even-involution
calculation therefore generates the whole starting stabilizer with one edge
kernel and the restricted endpoint actor. The controlled-actor bound shifts
any eligible seed backward and bounds its old slice by two when the shifted
critical image is small.

Two successive generating shifts contradict the three-pair commutator
calculation. Thus the backward shift of a large critical pair is small. All
eligible slices of that large pair then have index at most two, contradicting
the strict slice of its shifted small pair after transport to the same edge.
Every critical image is consequently of order two and every forward slice is
strict. The paired backward construction and its three-shift consumer now have
both their critical-image and strict-slice premises discharged, including when
the original radical is Sylow.

Both moved covers, all X/Z/U central attachments, the original radical and its
minimum characteristic replacement, and the actual natural graph are retained.
The import-all edges reuse the internal even-actor generation, controlled-kernel
bound and paired-path transport without changing the earlier public boundaries.
No identification with the exceptional graph or its kernels is used.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.5)--(5.11), printed pp.915--924. Terminal elementary-image exclusion,
non-elementary Sylow images and distance four remain with this assembly; the
unconditional replacement-distance bound is not established by this module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

namespace SylowCritical

include e hz hn in
private theorem elementary_large_image_controlled_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ W : Subgroup (FreeAmalgam d.radical), W ≤ U d.radical a' ∧
      ⁅V d.radical (alpha d.radical) ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),W⁆ ≤
        Z d.radical (alpha d.radical) ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,a,ha,hao,haeven⟩ := critical_radius_even_actor s hc hb2 p hlarge
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) :=
    (hWU.trans (DistanceEight.U_le_Z d.radical a')).trans
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
        (replacementDistance_pos h d) p.critical)
  obtain ⟨u,hu⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hu
  have himages : (∃ u : Equiv.Perm (Fin 6), d.radical.map s.projection =
      pointCore.map (MulAut.conj u).toMonoidHom) ∨
      (∃ u : Equiv.Perm (Fin 6), d.radical.map s.projection =
        (D 6).map (MulAut.conj u).toMonoidHom) := Or.inr ⟨u,hu⟩
  refine ⟨W,hWU,hbound,?_,generating_neighbor_of_even_actor s himages W hWG a ha hao haeven⟩
  intro hWQ
  have hWker : W.comap (embedM d.radical) ≤ s.projection.ker := by
    rw [s.projection_kernel]
    have hh := comap_mono (f := embedM d.radical) hWQ
    rwa [Q_alpha_comap d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hh
  have hbot := (Subgroup.map_eq_bot_iff (W.comap (embedM d.radical))).mpr hWker
  have hone : a=1 := by
    have hh : a ∈ (⊥ : Subgroup (Equiv.Perm (Fin 6))) := hbot ▸ ha
    exact hh
  rw [hone,orderOf_one] at hao
  omega

include e hz hn in
private theorem elementary_large_image_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hel : ¬ U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) (act d.radical g delta)
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ k ≤ p.walk.length-2, q.walk.getVert (k+2) = p.walk.getVert k) ∧
          ((Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
              (Z d.radical (act d.radical g delta)) < 4 →
            (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
              (U d.radical delta) = 2) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hWU,hbound,hWne,t,hat,hgen⟩ := elementary_large_image_controlled_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hlarge
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have ha1 : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) ha1 hat
  let c := act d.radical g delta
  have hct : Adjacent d.radical c t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g delta (p.walk.getVert 1)).mpr hdelta
  have hcol : color d.radical c = false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hct
    change false ≠ color d.radical t at h1
    cases hc : color d.radical c <;> cases ht : color d.radical t <;> simp_all
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hg))
  have helc : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
    intro hh
    apply hel
    change U d.radical (act d.radical g delta) ≤ _ at hh
    rw [U_act,←hB] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  have hbad : ¬ Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply helc
    apply (DistanceEight.U_le_Z d.radical c).trans
    apply backward_kernel_le_slice_of_controlled_actor s hb2 p W hWU hWne hbound hat hct hgen
      (Z d.radical c) le_rfl hbad
    exact (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Z_normalized d.radical c)
  let w : (cosetGraph d.radical).Walk c (alpha d.radical) :=
    .cons ((cosetGraph_adj d.radical _ _).mpr hct)
      (.cons ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (by exact Nat.le_of_lt hb2) hcol w hw hbad
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  have hgenZ : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm d.radical hat))
        (critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
          (replacementDistance_pos h d) p.critical)
    · rw [←hgen]
      exact sup_le_sup_left (hWU.trans (DistanceEight.U_le_Z d.radical a')) _
  refine ⟨t,hat,hgenZ,g,hg,hgt,q,hqt,fun i hi => p.prepend_two_overlap _ _ _ _ _ hi,?_⟩
  intro hsmall
  have hE := hEimage
  rw [←SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hE
  let := hE
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAn := (small_critical_end_kernels_normalized_of_abelian_image s hc hab q hsmall).1
  rw [hqt] at hAn
  have hkernel := backward_kernel_le_slice_of_controlled_actor s hb2 p W hWU hWne hbound hat hct hgen
    (Z d.radical c ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)))
    inf_le_left inf_le_right hAn
  let := finite_Z d.radical c
  have hidx := relIndex_le_of_le_left hkernel
    (index_ne_zero_of_finite (H := (Z d.radical c ⊓
      Q d.radical (p.walk.getVert (p.walk.length-2))).subgroupOf (Z d.radical c)))
  rw [inf_relIndex_left] at hidx
  have hbound := ((relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
    index_ne_zero_of_finite).trans hidx).trans_eq (small_critical_indices s hc q hsmall).1
  change (B d.radical (alpha d.radical) _).relIndex (U d.radical (act d.radical g delta)) ≤ 2 at hbound
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hbound
  let := finite_Z d.radical delta
  let : Finite (U d.radical delta) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical delta)) (inclusion_injective _)
  have hp : 0 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hn : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≠ 1 := fun he => hel (relIndex_eq_one.mp he)
  omega

include e hz hn in
private theorem elementary_large_backward_step_base
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) :
    ∃ c t x, x ∈ stabilizer d.radical (alpha d.radical) ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hel := critical_forward_not_le_slice_of_escape s hc hb2
    (SylowEscape.elementary_criticalEscape_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage) p
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover,_⟩ :=
    elementary_large_image_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hEimage p hlarge hdelta hel
  refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hqt,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff d.radical x _ _).mpr hdelta

include e hz hn in
private theorem elementary_large_backward_step_at_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ c t x, x ∈ stabilizer d.radical a ∧
      act d.radical x (p.walk.getVert 2) = c ∧
      Adjacent d.radical a t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := elementary_large_backward_step_base (e := e) (hz := hz) (hn := hn) hb hEimage
    (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) (by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge)
  change act d.radical x ((actWalk d.radical g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex d.radical) :
      act d.radical y v = act d.radical g (act d.radical x (act d.radical g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g c)
      (act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act d.radical g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act d.radical g) hq1
    · intro i hi
      have he := congrArg (act d.radical g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act d.radical g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act d.radical g ((actWalk d.radical g⁻¹ p.walk).getVert
      ((actWalk d.radical g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act d.radical g c,act d.radical g t,y,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act d.radical y a = a
    rw [hy,show act d.radical x (act d.radical g⁻¹ a) = act d.radical g⁻¹ a from hx,hcancel]
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff d.radical g _ _).mpr hat
  · exact (adjacent_act_iff d.radical g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he

include e hz hn in
private theorem elementary_generating_backward_shift_indices_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      (Q d.radical q.start).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hsmall : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z d.radical q.start) < 4 := by
    by_contra! hlarge
    obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,r,hr1,hro⟩ :=
      elementary_large_backward_step_at_knownSimple (e := e) (hz := hz) (hn := hn)
        hb hEimage q.path hlarge
    let r' : BackwardShift (h := h) q.path := ⟨c,t,x,hx,hxc,hat,hct,hgen,r,hr1,hro⟩
    obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage
    have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
      rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
    exact cube_two_backward_shifts_false s hc hb u hR p q r'
  have hi := small_critical_indices s hc q.path hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc q.path hsmall⟩

include e hz hn in
private theorem elementary_large_backward_small_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ∃ q : BackwardShift (h := h) p,
      (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical q.start) = 2 ∧
      (Q d.radical q.start).relIndex (Z d.radical (p.walk.getVert (p.walk.length-2))) = 2 ∧
      Nat.card (⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := by
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,v,hv1,hvo⟩ :=
    elementary_large_backward_step_at_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p hlarge
  let q : BackwardShift (h := h) p := ⟨c,t,x,hx,hxc,hat,hct,hgen,v,hv1,hvo⟩
  exact ⟨q,elementary_generating_backward_shift_indices_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q⟩

include e hz hn in
private theorem generating_overlap_small
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) c
      (p.walk.getVert (p.walk.length-2)))
    (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical a)
    (hq2 : q.walk.getVert 2 = a) :
    (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (Z d.radical c) < 4 := by
  by_contra! hlarge
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨r,_,_,_⟩ := elementary_large_backward_small_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage q hlarge
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hlenP : p.walk.length = replacementDistance h d := p.length_eq_b
  have hlenQ : q.walk.length = replacementDistance h d := q.length_eq_b
  have hdist1 : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.dist_end]
    omega
  have hdist2 : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := q.walk.getVert (q.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  let H := ⁅Z d.radical r.start,Z d.radical (q.walk.getVert (q.walk.length-2))⁆
  have hHe : H ≤ Z d.radical (q.walk.getVert (q.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hHend : H ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color]
    change (cosetGraph d.radical).dist (q.walk.getVert (q.walk.length-2)) a' < replacementDistance h d
    omega
  have hnc := critical_commutator_not_central_at_shift_vertex s hc r.path
    c t a a' (by rw [r.first]; exact r.adjacent_start) hct hgen hHend
    r.transporter r.transporter_mem (by simpa only [hq2] using r.start_eq)
  exact hnc (cube_backward_commutator_central s hc hb2 u hR q r)

include e hz hn in
private theorem large_first_edge_slice_bound
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)))
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1)) :
    (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta) ≤ 2 := by
  by_cases hel : U d.radical delta ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)
  · rw [relIndex_eq_one.mpr hel]
    decide
  obtain ⟨t,_,hgen,g,_,hgt,q,_,hover,hsmall⟩ :=
    elementary_large_image_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hEimage p hlarge hdelta hel
  have hct : Adjacent d.radical (act d.radical g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff d.radical g _ _).mpr hdelta
  have hq2 : q.walk.getVert 2 = alpha d.radical := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  exact (hsmall (generating_overlap_small (e := e) (hz := hz) (hn := hn)
    hb hEimage p q hct hgen hq2)).le

include e hz hn in
private theorem large_critical_image_false_base
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨q,hi,_,_⟩ := elementary_large_backward_small_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p hlarge
  obtain ⟨g,hgc⟩ := exists_mVertex_of_color d.radical q.path.start_color
  have hbase : act d.radical g⁻¹ q.start = alpha d.radical := by
    rw [hgc,act_mVertex,mul_inv_cancel]
    rfl
  have q₀ := q.path.act g⁻¹
  rw [hbase] at q₀
  have hsmall₀ : (Q d.radical (act d.radical g⁻¹ (p.walk.getVert (p.walk.length-2)))).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    have hZ : Z d.radical (alpha d.radical) =
        (Z d.radical q.start).map (MulAut.conj g).toMonoidHom := by
      calc
        Z d.radical (alpha d.radical) = Z d.radical (act d.radical g⁻¹ q.start) :=
          congrArg (Z d.radical) hbase.symm
        _ = _ := by rw [Z_act,inv_inv]
    rw [hZ,Q_act,inv_inv,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective,hi]
    decide
  have hstrict := SylowStrict.elementary_small_forward_slice_strict_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage q₀ hsmall₀
  have hlp : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hlq : 2 < q₀.walk.length := q₀.length_eq_b ▸ hb2
  have hatp : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hatq : Adjacent d.radical (alpha d.radical) (q₀.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q₀.walk.adj_getVert_succ (i := 0) (by omega)
  have hδq : Adjacent d.radical (q₀.walk.getVert 2) (q₀.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (q₀.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors d.radical (alpha d.radical) hatq hatp
  have hδ : Adjacent d.radical (act d.radical x (q₀.walk.getVert 2)) (p.walk.getVert 1) := by
    rw [←hxt]
    exact (adjacent_act_iff d.radical x _ _).mpr hδq
  have hbound := large_first_edge_slice_bound (e := e) (hz := hz) (hn := hn) hb hEimage p hlarge hδ
  have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 (alpha d.radical) rfl ((stabilizer d.radical (alpha d.radical)).inv_mem hx))
  rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hbound
  omega

include e hz hn in
/-- Large critical images are impossible above distance four for an elementary
replacement image, with no nonsylow hypothesis on the original radical. -/
theorem elementary_large_critical_image_false_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hlarge : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) : False := by
  obtain ⟨g,hga⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hga,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_critical_image_false_base (e := e) (hz := hz) (hn := hn)
    hb hEimage (a' := act d.radical g⁻¹ a')
  rw [←hbase] at base
  apply base (p.act g⁻¹)
  rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
  exact hlarge

include e hz hn in
/-- Every critical pair has both seed images and its full commutator of
order two in the elementary replacement-image branch above distance four. -/
theorem elementary_critical_indices_two_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
      (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
      Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  have hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4 := by
    by_contra! hlarge
    exact elementary_large_critical_image_false_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage p hlarge
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := small_critical_indices s hc p hsmall
  exact ⟨hi.1,hi.2,small_critical_commutator_card s hc p hsmall⟩

include e hz hn in
/-- Every forward slice is strict; the critical-image premise of the
small-image strict-slice theorem is discharged. -/
theorem elementary_forward_slice_strict_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2)) := by
  apply SylowStrict.elementary_small_forward_slice_strict_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p
  rw [(elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).1]
  decide

include e hz hn in
private theorem paired_backward_shift_base
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    Nonempty (PairedBackwardShift (h := h) p) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb2
  have hdelta : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by
    rw [(elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).1]
    decide
  obtain ⟨u,hu⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  obtain ⟨t,hat,g,hg,hgt,hct,_,x,hx,hpair,hx3,q,hq,_,hgen,halt⟩ :=
    SylowSmall.cube_small_backward_selection_knownSimple (e := e) (hz := hz) (hn := hn)
      hb2 u hu p hsmall hdelta
      (elementary_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p)
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · exact ⟨⟨_,t,g,hg,hgt,rfl,hat,hct,x,hx,hx3,hpair,hgen,v,hvt,hover⟩⟩
  · let y := g*x⁻¹
    have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
    have hy : y ∈ stabilizer d.radical (alpha d.radical) := mul_mem hg (inv_mem hxG)
    have hfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hxG
    have hat' : Adjacent d.radical (alpha d.radical) (act d.radical x⁻¹ t) := by
      rw [←hfix]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
    have hyt : act d.radical y (p.walk.getVert 1) = act d.radical x⁻¹ t := by
      rw [show y=g*x⁻¹ from rfl,act_mul,hgt]
    have hstart : act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)) =
        act d.radical y (p.walk.getVert 2) := (act_mul d.radical g x⁻¹ _).symm
    have hct' : Adjacent d.radical (act d.radical y (p.walk.getVert 2))
        (act d.radical x⁻¹ t) := by
      rw [←hstart]
      exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
    have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
        p.walk.getVert (p.walk.length-2) := by
      rw [hlen,hq,←act_mul,mul_inv_cancel,act_one]
    have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical y (p.walk.getVert 2)) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 1=act d.radical x⁻¹ t ∧
        ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g (p.walk.getVert 2)))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 1=act d.radical x⁻¹ t ∧
          ∀ i ≤ p.walk.length-2, w.walk.getVert (i+2)=p.walk.getVert i := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · simp only [CriticalPath.act,actWalk_getVert,hvt]
        · intro i hi
          simp only [CriticalPath.act,actWalk_getVert,hover i (hlen.symm ▸ hi),hq,
            ←act_mul,mul_inv_cancel,act_one]
      rwa [hstart,hend] at hex
    obtain ⟨w,hw1,hwo⟩ := hex
    refine ⟨⟨_,_,y,hy,hyt,rfl,hat',hct',x⁻¹,inv_mem hx,?_,?_,?_,w,hw1,hwo⟩⟩
    · simpa only [inv_pow] using (Q d.radical (alpha d.radical)).inv_mem hx3
    · rw [Q_act,inv_inv,map_map]
      have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id (FreeAmalgam d.radical) := by
        apply MonoidHom.ext
        intro z
        change x⁻¹*(x*z*x⁻¹)*(x⁻¹)⁻¹=z
        group
      rw [he,map_id]
      exact (sup_comm _ _).trans hpair
    · have hQt : (Q d.radical t).map (MulAut.conj x).toMonoidHom =
          Q d.radical (act d.radical x⁻¹ t) := by rw [Q_act,inv_inv]
      have hZa (z : Vertex d.radical) : (Z d.radical z).map (MulAut.conj x).toMonoidHom =
          Z d.radical (act d.radical x⁻¹ z) := by rw [Z_act,inv_inv]
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hgen
      simp only [Subgroup.map_sup,hQt,hZa,hGa,←act_mul,mul_inv_cancel,act_one] at hh
      calc
        _ = Q d.radical (act d.radical x⁻¹ t) ⊔ Z d.radical (act d.radical x⁻¹ a') ⊔
          Z d.radical a' := by ac_rfl
        _ = _ := hh

include e hz hn in
/-- The actual repeated backward selection retains the cubic, both
generation equations and all overlaps at every original component vertex. -/
theorem elementary_paired_backward_shift_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Nonempty (PairedBackwardShift (h := h) p) := by
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical j⁻¹ a = alpha d.radical := by
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := paired_backward_shift_base (e := e) (hz := hz) (hn := hn)
    hb hEimage (a' := act d.radical j⁻¹ a')
  rw [←hbase] at base
  obtain ⟨q⟩ := base (p.act j⁻¹)
  have hcancel (v : Vertex d.radical) : act d.radical j (act d.radical j⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  exact paired_backward_shift_of_vertices p ((p.act j⁻¹).act j)
    (hcancel a) (hcancel a') (by
      intro i
      simp only [CriticalPath.act,actWalk_getVert,hcancel]) (q.conjugate j)

include e hz hn in
/-- The shifted critical line lies in the selected edge and starting seeds
and centralizes the full old endpoint radius, retaining its own noncentrality. -/
theorem elementary_paired_shift_commutator_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p) :
    let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
    Nat.card H = 2 ∧ H ≤ Z d.radical q.edge ∧ H ≤ Z d.radical a ∧
      H ≤ centralizer (Q d.radical q.edge : Set (FreeAmalgam d.radical)) ∧
      H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) ∧
      ¬ H ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  let H := ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hHt : H ≤ Z d.radical q.edge := by
    simpa only [q.first] using cube_critical_commutator_le_first_seed s hc u hR q.path
  have hHe : H ≤ Z d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hHQ : H ≤ centralizer (Q d.radical q.edge : Set (FreeAmalgam d.radical)) := by
    intro x hx
    have hh := hHt hx
    rw [Z,if_neg (by simp [ht])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hVQ : V d.radical a' ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    change (cosetGraph d.radical).dist a' (p.walk.getVert (p.walk.length-2)) + 2 <
      replacementDistance h d
    rw [SimpleGraph.dist_comm,p.dist_end]
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    omega
  have hHV : H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) :=
    (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical _ q.path.end_color))).trans (centralizer_le hVQ)
  exact ⟨(elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn)
      hb hEimage q.path).2.2,hHt,hHt.trans (adjacent_Z_le d.radical p.start_color q.adjacent_start),
    hHQ,hHV,critical_commutator_not_central s hc q.path⟩

include e hz hn in
/-- Three actual paired shifts supply the source R₄ and R₆ lines with
both generation equations, their radius centrality and their noncentrality. -/
theorem elementary_three_paired_shifts_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : PairedBackwardShift (h := h) p,
      ∃ r : PairedBackwardShift (h := h) q.path,
        ∃ t : PairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          Nat.card R₄ = 2 ∧ Nat.card R₆ = 2 ∧
          R₄ ≤ Z d.radical r.edge ⊓ Z d.radical q.start ∧
          R₆ ≤ Z d.radical t.edge ⊓ Z d.radical r.start ∧
          R₄ ⊔ R₆ ≤ centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) ∧
          R₄ ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) ∧
          ¬ R₄ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) ∧
          ¬ R₆ ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := by
  obtain ⟨q⟩ := elementary_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p
  obtain ⟨r⟩ := elementary_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage q.path
  obtain ⟨t⟩ := elementary_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage r.path
  have hr := elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage q.path r
  have ht := elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage r.path t
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
  have hR₄Z : R₄ ≤ Z d.radical z₄ :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hR₄V : R₄ ≤ centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) :=
    (hR₄Z.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z₄ r.path.end_color))).trans
        (centralizer_le (V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
          (by change 2 < replacementDistance h d; omega)))
  have hnear : (cosetGraph d.radical).dist z₄ a' ≤ 4 := by
    have h₁ : (cosetGraph d.radical).dist z₄ (p.walk.getVert (p.walk.length-2))=2 := by
      rw [q.path.dist_end]
      have hl : q.path.walk.length=replacementDistance h d := q.path.length_eq_b
      omega
    have h₂ : (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a'=2 := by
      rw [p.dist_end]
      have hl : p.walk.length=replacementDistance h d := p.length_eq_b
      omega
    have hh := (cosetGraph_connected d.radical).dist_triangle
      (u := z₄) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  have hR₄end : R₄ ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply (hR₄Z.trans (Z_le_Q_of_dist_lt d.radical _
      ((replacementGeometry h d).exists_critical z₄ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)))
    rw [(replacementGeometry h d).distance_constant z₄ r.path.end_color]
    change (cosetGraph d.radical).dist z₄ a' < replacementDistance h d
    omega
  exact ⟨q,r,t,hr.1,ht.1,le_inf hr.2.1 hr.2.2.1,le_inf ht.2.1 ht.2.2.1,
    sup_le hR₄V ht.2.2.2.2.1,hR₄end,hr.2.2.2.2.2,ht.2.2.2.2.2⟩

end SylowCritical
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
