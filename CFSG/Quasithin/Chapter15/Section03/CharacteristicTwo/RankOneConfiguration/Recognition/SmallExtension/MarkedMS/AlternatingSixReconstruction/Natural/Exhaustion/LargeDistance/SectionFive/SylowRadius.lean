module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowPaired
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusAction
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeIntermediateLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusDisplacement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCentralIntersection

/-!
# The terminal radius alternative for elementary replacement images

The paired paths from SylowPaired give the literal R4/R6 critical lines.
A large image of the common endpoint radius forces intermediate centrality
by the marked three-pair fixed-vector calculation. At distance six the two
selected kernels immediately contradict that centrality. Above six, the
full radius kernel produces a commutator plane; its central intersection
transfers along the same path. This forces a radius of index four.

These are the CubeRadiusAction, CubeIntermediateLine, CubeRadiusDisplacement,
CubeRadiusPlane and CubeCentralIntersection arguments with their original
nonsylow premise replaced by the proved elementary-image producers. The
additional old-first-edge generation is constructed in SylowPaired. Every
radius, kernel, central attachment and transporter is the original one;
neither a single-endpoint generation equation nor an exceptional graph is
substituted. The private imports reuse the existing local group lemmas.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10)--(5.11), printed pp.922--924, in particular the common-radius
comparison and the central intersection in the terminal argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace SylowTerminal
open CubePairedEdges CubeCommonFixer CubeRadiusAction NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include e hz hn in
/-- The original and selected edge kernels now turn large-actor fixedness
into centrality of the selected critical line at the intermediate vertex. -/
theorem elementary_edge_paired_line_central_of_large_actor_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (A : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ Q d.radical (p.walk.getVert 1))
    (hlarge : 2 < (Q d.radical a).relIndex A)
    (hfixed : ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (A : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (p.length_eq_b ▸ replacementDistance_pos h d)
  have hline := SylowCritical.elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hEimage p q.toPairedBackwardShift
  have hfirst := (le_inf hline.2.2.1 hfixed).trans
    (cube_edge_large_fixed_le_seed s hc u hR p.start_color hat A hA hlarge)
  exact (le_inf hfirst hline.2.1).trans q.edge_seed_intersection_central

include e hz hn in
/-- The two source-(5.11) action comparisons use the very same endpoint
radius. Its full image controls the first shifted line; its intersection
with the preceding core controls the next line. Both conclusions are at
the intermediate stabilizers, with both paired edge kernels accounted for. -/
theorem elementary_edge_paired_same_radius_actions_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path) :
    let z := p.walk.getVert (p.walk.length-2)
    let H := ⁅Z d.radical q.start,Z d.radical z⁆
    let K := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
    (2 < (Q d.radical a).relIndex (V d.radical z) →
      H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
    (2 < (Q d.radical q.start).relIndex (V d.radical z ⊓ Q d.radical a) →
      K ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) := by
  let z := p.walk.getVert (p.walk.length-2)
  let H := ⁅Z d.radical q.start,Z d.radical z⁆
  have hHQ : H ≤ centralizer (Q d.radical z : Set (FreeAmalgam d.radical)) :=
    (((critical_Z_commutator_le_moving (h := h) q.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical z)).trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical z q.path.end_color))
  have hHV : H ≤ centralizer (V d.radical z : Set (FreeAmalgam d.radical)) :=
    hHQ.trans (centralizer_le (V_le_Q d.radical (geometry := replacementGeometry h d)
      q.path.end_color (by change 2 < replacementDistance h d; omega)))
  have hVedge : V d.radical z ≤ Q d.radical (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) q.path.end_color
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert,show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph d.radical).dist z (p.walk.getVert 1)+2 < replacementDistance h d
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  have hedge : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hAedge : V d.radical z ⊓ Q d.radical a ≤ Q d.radical (q.path.walk.getVert 1) := by
    rw [q.first]
    exact inf_le_right.trans (Q_le_adjacent_h d.radical hedge q.adjacent_start)
  have hKfixed := (SylowCritical.elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hEimage q.path r.toPairedBackwardShift).2.2.2.2.1
  constructor
  · intro hlarge
    exact elementary_edge_paired_line_central_of_large_actor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage p q (V d.radical z) hVedge hlarge hHV
  · intro hlarge
    exact elementary_edge_paired_line_central_of_large_actor_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage q.path r
      (V d.radical z ⊓ Q d.radical a) hAedge hlarge
      (hKfixed.trans (centralizer_le inf_le_left))

include e hz hn in
/-- The original elementary-image replacement supplies the actual terminal plane
and both same-radius action estimates in one coherent three-shift chain.
The strict radius bound and intermediate noncentrality remain separate
source obligations; they are not hypotheses hidden in this construction. -/
theorem elementary_edge_paired_terminal_radius_actions_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      ∃ r : EdgePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam d.radical)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z d.radical r.start ⊓
            centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) ∧
          (2 < (Q d.radical q.start).relIndex (V d.radical z₄) →
            R₄ ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
          (2 < (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) →
            R₆ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) := by
  obtain ⟨q,r,t,hdis,hcard,hplane⟩ := elementary_edge_paired_terminal_plane_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p
  have hact := elementary_edge_paired_same_radius_actions_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage q.path r t
  exact ⟨q,r,t,hdis,hcard,hplane,hact⟩

include e hz hn in
/-- If the second shifted line were central at the intervening vertex, the
literal transporter would put it in the original seed, noncentrally, and
in the first backward edge seed. -/
theorem elementary_edge_paired_intermediate_central_transport_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) :
    let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
    H ≤ Z d.radical a ∧ H ≤ Z d.radical q.edge ∧
      ¬ H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
  have hline := SylowCritical.elementary_paired_shift_commutator_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hEimage q.path r.toPairedBackwardShift
  have hstart : act d.radical r.transporter a = r.start := by
    have hqa : q.path.walk.getVert 2=a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
    simpa only [hqa] using r.start_eq
  have hfixed : H.map (MulAut.conj r.transporter⁻¹).toMonoidHom = H :=
    central_fixed_map H (stabilizer d.radical q.start) hcentral
      ((stabilizer d.radical q.start).inv_mem r.transporter_mem)
  have hHZ : H ≤ Z d.radical a := by
    have hh : H ≤ Z d.radical r.start :=
      ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    rw [←hstart,Z_act,←hfixed] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj r.transporter⁻¹).injective).mp hh
  refine ⟨hHZ,central_line_le_neighbor r.adjacent_start q.adjacent_shift H hcentral hline.2.1,?_⟩
  intro hHa
  apply hline.2.2.2.2.2
  have hh := (map_mono (f := (MulAut.conj r.transporter⁻¹).toMonoidHom) hHa).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [hfixed] at hh
  change H ≤ centralizer ((stabilizer d.radical a).map
    (MulAut.conj r.transporter⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
  rwa [←stabilizer_act,hstart] at hh

include e hz hn in
/-- At distance six the same critical line is noncentral at the required
intermediate stabilizer, not just at its own critical start. -/
theorem elementary_edge_paired_intermediate_noncentral_six_knownSimple
    (hb : replacementDistance h d = 6)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path) :
    ¬ ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  obtain ⟨hHZ,hHedge,hnon⟩ := elementary_edge_paired_intermediate_central_transport_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega) hEimage p q r hcentral
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  let rev : CriticalPath d.radical (replacementGeometry h d)
      (q.path.walk.getVert (q.path.walk.length-2)) r.start :=
    ⟨r.path.end_color,r.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,r.path.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc r.path⟩
  have hlast := cube_critical_commutator_le_first_seed s hc u hR rev
  change ⁅Z d.radical (q.path.walk.getVert (q.path.walk.length-2)),Z d.radical r.start⁆ ≤
    Z d.radical (r.path.walk.reverse.getVert 1) at hlast
  rw [commutator_comm,SimpleGraph.Walk.getVert_reverse] at hlast
  have hlp : p.walk.length=6 := p.length_eq_b.trans hb
  have hlq : q.path.walk.length=6 := q.path.length_eq_b.trans hb
  have hlr : r.path.walk.length=6 := r.path.length_eq_b.trans hb
  have he : r.path.walk.getVert (r.path.walk.length-1)=p.walk.getVert 1 := by
    rw [hlr,show 6-1=3+2 from rfl,r.overlap 3 (by omega),
      show 3=1+2 from rfl,q.overlap 1 (by omega)]
  rw [he] at hlast
  exact hnon ((le_inf hlast hHedge).trans q.edge_seed_intersection_central)

include e hz hn in
/-- Above distance six, intermediate centrality would force the exact
source-(5.11) two-element image of the two indicated radius actors at the
original vertex. The endpoint radius and its next-core intersection are
kept in the same graph and the same join. -/
theorem elementary_edge_paired_intermediate_central_radius_index_knownSimple
    (hb : 6 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) :
    (Q d.radical a).relIndex (V d.radical (p.walk.getVert (p.walk.length-2)) ⊔
      (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2))) = 2 := by
  let H := ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆
  let z₂ := p.walk.getVert (p.walk.length-2)
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  let A := V d.radical z₂ ⊔ (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2))
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨hHZ,hHedge,hnon⟩ := elementary_edge_paired_intermediate_central_transport_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hEimage p q r hcentral
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hEimage
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hlp : p.walk.length=replacementDistance h d := p.length_eq_b
  have hlq : q.path.walk.length=replacementDistance h d := q.path.length_eq_b
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ
      (i := 0) (by omega)
  have hpt : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical (p.walk.getVert 1)=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical (p.walk.getVert 1) <;> simp_all
  have hVedge : V d.radical z₂ ≤ Q d.radical (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) q.path.end_color
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert,show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph d.radical).dist z₂ (p.walk.getVert 1)+2 < replacementDistance h d
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  have hA : A ≤ Q d.radical (p.walk.getVert 1) :=
    sup_le hVedge (inf_le_right.trans (Q_le_adjacent_h d.radical ht hpt))
  have hHe : H ≤ Z d.radical z₄ :=
    ((critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical _)
  have hd₂ : (cosetGraph d.radical).dist z₂ z₄ = 2 := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (q.path.walk.getVert (q.path.walk.length-2)) _ = 2
    rw [q.path.dist_end]
    omega
  have hd₀ : (cosetGraph d.radical).dist a' z₂ = 2 := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) _ = 2
    rw [p.dist_end]
    omega
  have hd₄ : (cosetGraph d.radical).dist a' z₄ ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := a') (v := z₂) (w := z₄)
    omega
  have hV₂ : V d.radical z₂ ≤ Q d.radical z₄ := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) q.path.end_color
    change (cosetGraph d.radical).dist z₂ z₄+2 < replacementDistance h d
    omega
  have hV₀ : V d.radical a' ≤ Q d.radical z₄ := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    change (cosetGraph d.radical).dist a' z₄+2 < replacementDistance h d
    omega
  have hHA : H ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    (hHe.trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z₄ r.path.end_color))).trans
        (centralizer_le (sup_le hV₂ (inf_le_left.trans hV₀)))
  have hupper : (Q d.radical a).relIndex A ≤ 2 := by
    by_contra! hlarge
    exact hnon ((le_inf ((le_inf hHZ hHA).trans
      (cube_edge_large_fixed_le_seed s hc u hR p.start_color hat A hA hlarge)) hHedge).trans
        q.edge_seed_intersection_central)
  let rev : CriticalPath d.radical (replacementGeometry h d) z₂ q.start :=
    ⟨q.path.end_color,q.path.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.path.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q.path⟩
  have hescape := SylowEscape.elementary_radius_escape_at_knownSimple (e := e) (hz := hz) (hn := hn)
    hb4 hEimage rev
  have hqa : q.path.walk.getVert 2=a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  change ¬ V d.radical z₂ ≤ Q d.radical
    (q.path.walk.reverse.getVert (q.path.walk.reverse.length-2)) at hescape
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show q.path.walk.length-(q.path.walk.length-2)=2 by omega,hqa] at hescape
  have hne : (Q d.radical a).relIndex A ≠ 1 := fun hh =>
    hescape (le_sup_left.trans (relIndex_eq_one.mp hh))
  let := finite_stabilizer d.radical (p.walk.getVert 1)
  let : Finite A := Finite.of_injective
    (inclusion (hA.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hpos : 0 < (Q d.radical a).relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
  change (Q d.radical a).relIndex A=2
  omega

include e hz hn in
/-- In the literal three-shift chain at distance six, both terminal lines
are noncentral at the intervening stabilizers. The existing same-radius
action implications force the opposite radius index to equal four. -/
theorem elementary_edge_paired_terminal_six_knownSimple
    (hb : replacementDistance h d = 6)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ∃ q : EdgePairedBackwardShift (h := h) p,
      ∃ r : EdgePairedBackwardShift (h := h) q.path,
        ∃ t : EdgePairedBackwardShift (h := h) r.path,
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          let z₆ := r.path.walk.getVert (r.path.walk.length-2)
          let R₄ := ⁅Z d.radical r.start,Z d.radical z₄⁆
          let R₆ := ⁅Z d.radical t.start,Z d.radical z₆⁆
          R₄ ⊓ R₆ = ⊥ ∧ Nat.card (R₄ ⊔ R₆ : Subgroup (FreeAmalgam d.radical)) = 4 ∧
          R₄ ⊔ R₆ ≤ Z d.radical r.start ⊓
            centralizer (V d.radical z₄ : Set (FreeAmalgam d.radical)) ∧
          (¬ R₄ ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))) ∧
          (¬ R₆ ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) ∧
          (Q d.radical r.start).relIndex (V d.radical z₄) = 4 := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨q,r,t,hdis,hcard,hplane,hact₄,hact₆⟩ := elementary_edge_paired_terminal_radius_actions_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hEimage p
  have hn₄ := elementary_edge_paired_intermediate_noncentral_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q r
  have hn₆ := elementary_edge_paired_intermediate_noncentral_six_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage q.path r t
  refine ⟨q,r,t,hdis,hcard,hplane,hn₄,hn₆,?_⟩
  let z₄ := q.path.walk.getVert (q.path.walk.length-2)
  have hi₄ : (Q d.radical q.start).relIndex (V d.radical z₄) ≤ 2 := by
    by_contra! hh
    exact hn₄ (hact₄ hh)
  have hi₆ : (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) ≤ 2 := by
    by_contra! hh
    exact hn₆ (hact₆ hh)
  have hVQ : V d.radical z₄ ≤ Q d.radical z₄ :=
    V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
      (by change 2 < replacementDistance h d; omega)
  let := finite_stabilizer d.radical z₄
  let : Finite (V d.radical z₄) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have htower := relIndex_inf_mul_relIndex (Q d.radical r.start) (Q d.radical q.start) (V d.radical z₄)
  rw [inf_comm (Q d.radical q.start)] at htower
  have hmono : (Q d.radical r.start).relIndex (V d.radical z₄) ≤
      (Q d.radical r.start ⊓ Q d.radical q.start).relIndex (V d.radical z₄) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hupper : (Q d.radical r.start).relIndex (V d.radical z₄) ≤ 4 := by
    rw [←htower] at hmono
    exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
  exact (small_opposite_radius_eq_four_knownSimple (e := e) (hz := hz) (hn := hn)
    (by omega) r.path hupper).2.2

include e hz hn in
/-- The exact source H and both radius actors on the original paired chain.
The strict endpoint-radius bounds remain the source premises to be proved. -/
theorem elementary_intermediate_central_radius_displacement_knownSimple
    (hb : 6 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)))
    (hstrict₀ : 4 < (Q d.radical a).relIndex (V d.radical a'))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2)))) :
    let A := V d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical a
    let H := ⁅Z d.radical q.start,A⁆
    2 < (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a') ∧
      2 < (Q d.radical q.start).relIndex A ∧
      4 ≤ (centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))).relIndex H ∧
      H ≤ Z d.radical a ∧ H ≤ V d.radical (p.walk.getVert (p.walk.length-2)) ∧
      H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) := by
  let z := p.walk.getVert (p.walk.length-2)
  let A := V d.radical z ⊓ Q d.radical a
  let H := ⁅Z d.radical q.start,A⁆
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hjoin := elementary_edge_paired_intermediate_central_radius_index_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p q r hcentral
  have hi : (Q d.radical a).relIndex (V d.radical z) ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q d.radical a)
      (show V d.radical z ≤ V d.radical z ⊔
        (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) from le_sup_left)
      (by rw [hjoin]; decide)
    exact hh.trans_eq hjoin
  have hi₀ : (Q d.radical a).relIndex
      (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) ≤ 2 := by
    have hh := relIndex_le_of_le_right (H := Q d.radical a)
      (show V d.radical a' ⊓ Q d.radical (p.walk.getVert 2) ≤ V d.radical z ⊔
        (V d.radical a' ⊓ Q d.radical (p.walk.getVert 2)) from le_sup_right)
      (by rw [hjoin]; decide)
    exact hh.trans_eq hjoin
  have hlarge₀ : 2 < (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a') := by
    have hVQ₀ : V d.radical a' ≤ Q d.radical a' :=
      V_le_Q d.radical (geometry := replacementGeometry h d) p.end_color
        (by change 2 < replacementDistance h d; omega)
    let := finite_stabilizer d.radical a'
    let : Finite (V d.radical a') := Finite.of_injective
      (inclusion (hVQ₀.trans (fun _ hx => hx.1))) (inclusion_injective _)
    by_contra! hsmall
    have htower := relIndex_inf_mul_relIndex (Q d.radical a)
      (Q d.radical (p.walk.getVert 2)) (V d.radical a')
    rw [inf_comm (Q d.radical (p.walk.getVert 2))] at htower
    have hmono : (Q d.radical a).relIndex (V d.radical a') ≤
        (Q d.radical a ⊓ Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a') :=
      relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
    rw [←htower] at hmono
    have hupper := hmono.trans (Nat.mul_le_mul hi₀ hsmall)
    omega
  have hVQ : V d.radical z ≤ Q d.radical z :=
    V_le_Q d.radical (geometry := replacementGeometry h d) q.path.end_color
      (by change 2 < replacementDistance h d; omega)
  let := finite_stabilizer d.radical z
  let : Finite (V d.radical z) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hlarge : 2 < (Q d.radical q.start).relIndex A := by
    by_contra! hsmall
    have htower := relIndex_inf_mul_relIndex (Q d.radical q.start) (Q d.radical a) (V d.radical z)
    rw [inf_comm (Q d.radical a)] at htower
    have hmono : (Q d.radical q.start).relIndex (V d.radical z) ≤
        (Q d.radical q.start ⊓ Q d.radical a).relIndex (V d.radical z) :=
      relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
    rw [←htower] at hmono
    have hupper := hmono.trans (Nat.mul_le_mul hsmall hi)
    change 4 < (Q d.radical q.start).relIndex (V d.radical z) at hstrict
    omega
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hAedge : A ≤ Q d.radical q.edge :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht q.adjacent_start)
  have hAG : A ≤ stabilizer d.radical q.start :=
    hAedge.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_shift))
  have hlower := graph_large_actor_seed_commutator_index s hc q.path.start_color A hAG hlarge
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hEimage
  have hR : d.radical.map s.projection ≤
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hHZ : H ≤ Z d.radical a :=
    ((commutator_mono le_rfl hAedge).trans
      (cube_edge_seed_commutator_le s hc u hR q.path.start_color q.adjacent_shift)).trans
        (adjacent_Z_le d.radical p.start_color q.adjacent_start)
  have hZG : Z d.radical q.start ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le q.start _ q.path.critical.1.le
  have hHV : H ≤ V d.radical z :=
    (commutator_mono le_rfl (show A ≤ V d.radical z from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (hZG.trans (DistanceEight.V_normalized d.radical z)))
  have hdist : (cosetGraph d.radical).dist z a'=2 := by
    change (cosetGraph d.radical).dist (p.walk.getVert (p.walk.length-2)) a'=2
    rw [p.dist_end]
    have hl : p.walk.length=replacementDistance h d := p.length_eq_b
    omega
  have hVV : V d.radical z ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) := by
    apply Escape.PairingControl.Geometry.V_centralizes_V_of_distance
      (geometry := replacementGeometry h d) q.path.end_color p.end_color
    change (cosetGraph d.radical).dist z a'+4 < replacementDistance h d
    omega
  exact ⟨hlarge₀,hlarge,hlower,hHZ,hHV,hHV.trans hVV⟩

include e hz hn in
/-- The source H fills the same natural commutator plane as the whole
backward edge kernel. Both strict radius premises remain explicit. -/
theorem elementary_intermediate_central_radius_plane_knownSimple
    (hb : 6 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : EdgePairedBackwardShift (h := h) p)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)))
    (hstrict₀ : 4 < (Q d.radical a).relIndex (V d.radical a'))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2)))) :
    let A := V d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical a
    let H := ⁅Z d.radical q.start,A⁆
    let C := Z d.radical q.start ⊓
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))
    (centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))).relIndex H = 4 ∧
      (Nat.card H = 4 ∨ Nat.card H = 8) ∧
      H ⊔ C = ⁅Z d.radical q.start,Q d.radical q.edge⁆ ⊔ C ∧
      H ≤ Z d.radical q.edge ∧ H ≤ Z d.radical a ∧
      H ≤ V d.radical (p.walk.getVert (p.walk.length-2)) ∧
      H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)) := by
  let A := V d.radical (p.walk.getVert (p.walk.length-2)) ⊓ Q d.radical a
  let H := ⁅Z d.radical q.start,A⁆
  obtain ⟨_,hlarge,_,hHZ,hHV,hfixed⟩ :=
    elementary_intermediate_central_radius_displacement_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage p q r hcentral hstrict₀ hstrict
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hEimage
  have hR : d.radical.map s.projection =
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hA : A ≤ Q d.radical q.edge :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht q.adjacent_start)
  have hplane := cube_graph_large_actor_commutator_plane s hc u hR
    q.path.start_color q.adjacent_shift A hA hlarge
  exact ⟨hplane.1,hplane.2.1,hplane.2.2,(commutator_mono le_rfl hA).trans
    (cube_edge_seed_commutator_le s hc u hR.le q.path.start_color q.adjacent_shift),hHZ,hHV,hfixed⟩

include e hz hn in
private theorem paired_fixed_seed_central_index
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (H : Subgroup (FreeAmalgam d.radical))
    (hHZ : H ≤ Z d.radical a) (hHe : H ≤ Z d.radical q.edge)
    (hHend : H ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))) :
    (centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))).relIndex H ≤ 2 := by
  let C := centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let K := Q d.radical (act d.radical q.cubic a')
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hHC : H ⊓ K ≤ C := by
    apply le_centralizer_iff.mpr
    rw [←q.endpoint_generation]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_centralizer_iff.mp
      intro x hx
      have he := hHe hx.1
      rw [Z,if_neg (by simp [ht])] at he
      exact (mem_omegaCenter_iff.mp he).2.2
    · exact le_centralizer_iff.mp (inf_le_left.trans hHend)
    · exact le_centralizer_iff.mp (inf_le_right.trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical _ ((action_preserves_color d.radical _ _).trans p.end_color)))))
  have hfix : act d.radical q.cubic a = a := Ltilde_le_stabilizer _ q.cubic_mem
  have hidx : K.relIndex (Z d.radical a)=2 := by
    change (Q d.radical (act d.radical q.cubic a')).relIndex (Z d.radical a)=2
    conv_lhs => rhs; rw [←hfix]
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj q.cubic⁻¹).injective]
    exact (SylowCritical.elementary_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hEimage p).1
  let := finite_Z d.radical a
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hi := relIndex_le_of_le_left hHC (index_ne_zero_of_finite (H := (H ⊓ K).subgroupOf H))
  rw [inf_relIndex_left] at hi
  exact hi.trans ((relIndex_le_of_le_right hHZ index_ne_zero_of_finite).trans_eq hidx)

include e hz hn in
private theorem paired_central_intersection_transfer
    (hb : 6 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2))
    (H : Subgroup (FreeAmalgam d.radical)) (hHc : H ≤ Z d.radical q.start)
    (hHend : H ≤ centralizer (V d.radical a' : Set (FreeAmalgam d.radical)))
    (hlarge : 2 < (Q d.radical (p.walk.getVert 2)).relIndex (V d.radical a')) :
    H ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  let H₀ := H ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨u,hfull⟩ := SylowSmall.four_lt_elementary_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) (d := d) (by omega) hEimage
  have hR : d.radical.map s.projection ≤
      (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hfixed : H₀.map (MulAut.conj q.transporter⁻¹).toMonoidHom = H₀ :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp (show H₀ ≤ centralizer
        (stabilizer d.radical a : Set (FreeAmalgam d.radical)) from inf_le_right)
          ((stabilizer d.radical a).inv_mem q.transporter_mem)))
  have hH₂ : H₀ ≤ Z d.radical (p.walk.getVert 2) := by
    have hh : H₀ ≤ Z d.radical q.start := inf_le_left.trans hHc
    rw [←q.start_eq,Z_act,←hfixed] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj q.transporter⁻¹).injective).mp hh
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have ha₂ : color d.radical (p.walk.getVert 2)=false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have h₂₃ : Adjacent d.radical (p.walk.getVert 2) (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have ha₃ : color d.radical (p.walk.getVert 3)=true := by
    have hh := adjacent_color_ne d.radical h₂₃
    rw [ha₂] at hh
    cases he : color d.radical (p.walk.getVert 3) <;> simp_all
  have hV₃ : V d.radical a' ≤ Q d.radical (p.walk.getVert 3) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) p.end_color
    rw [SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-3+2 < replacementDistance h d
    omega
  have hH₃ : H₀ ≤ Z d.radical (p.walk.getVert 3) :=
    (le_inf hH₂ (inf_le_left.trans hHend)).trans
      (cube_edge_large_fixed_le_seed s hc u hR ha₂ h₂₃ (V d.radical a') hV₃ hlarge)
  have hHC₂ : H₀ ≤ centralizer (stabilizer d.radical (p.walk.getVert 2) :
      Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    refine sup_le ?_ ?_
    · apply le_centralizer_iff.mp
      apply (inf_le_right : H₀ ≤ centralizer (stabilizer d.radical a : Set _)).trans
      apply centralizer_le
      intro x hx
      apply hx.2 a
      apply adjacent_symm d.radical
      apply (cosetGraph_adj d.radical _ _).mp
      simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
    · apply le_centralizer_iff.mp
      intro x hx
      have hh := hH₃ hx
      rw [Z,if_neg (by simp [ha₃])] at hh
      exact (mem_omegaCenter_iff.mp hh).2.2
  have hh := (map_mono (f := (MulAut.conj q.transporter⁻¹).toMonoidHom) hHC₂).trans
    (map_centralizer_le_centralizer_image _ _)
  change H₀.map (MulAut.conj q.transporter⁻¹).toMonoidHom ≤
    centralizer ((stabilizer d.radical (p.walk.getVert 2)).map
      (MulAut.conj q.transporter⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
  rwa [hfixed,←stabilizer_act,q.start_eq] at hh

include e hz hn in
/-- The central-intersection upper bound for the literal source H on the
paired chain. Both strict-radius premises are still required here. -/
theorem elementary_shifted_intermediate_central_radius_upper_knownSimple
    (hb : 6 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (v : EdgePairedBackwardShift (h := h) p)
    (q : EdgePairedBackwardShift (h := h) v.path)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hcentral : ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)))
    (hstrict₀ : 4 < (Q d.radical v.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))) :
    let H := ⁅Z d.radical q.start,
      V d.radical (v.path.walk.getVert (v.path.walk.length-2)) ⊓ Q d.radical v.start⁆
    (centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))).relIndex H ≤ 2 := by
  let H := ⁅Z d.radical q.start,
    V d.radical (v.path.walk.getVert (v.path.walk.length-2)) ⊓ Q d.radical v.start⁆
  obtain ⟨hlarge,_,_,hHZ,_,hHV⟩ :=
    elementary_intermediate_central_radius_displacement_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage v.path q r hcentral hstrict₀ hstrict
  obtain ⟨_,_,_,hHe,_,_,_⟩ := elementary_intermediate_central_radius_plane_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage v.path q r hcentral hstrict₀ hstrict
  have hHc : H ≤ Z d.radical q.start :=
    hHe.trans (adjacent_Z_le d.radical q.path.start_color q.adjacent_shift)
  have hi := paired_fixed_seed_central_index (e := e) (hz := hz) (hn := hn)
    (by omega) hEimage v.path q.toPairedBackwardShift H hHZ hHe
      (hHV.trans (centralizer_le (Z_le_VBall d.radical _ 2)))
  have htransfer := paired_central_intersection_transfer (e := e) (hz := hz) (hn := hn)
    hb hEimage v.path q.toPairedBackwardShift (v.first_interior_generation (by omega)) H hHc hHV hlarge
  let := finite_Z d.radical v.start
  let : Finite H := Finite.of_injective (inclusion hHZ) (inclusion_injective _)
  have hup := relIndex_le_of_le_left htransfer (index_ne_zero_of_finite
    (H := (H ⊓ centralizer (stabilizer d.radical v.start : Set (FreeAmalgam d.radical))).subgroupOf H))
  rw [inf_relIndex_left] at hup
  exact hup.trans hi

include e hz hn in
/-- Strict growth at the two successive radii excludes intermediate
centrality above six. The preceding paired shift discharges the required
interior generation, on the same original graph. -/
theorem elementary_shifted_intermediate_noncentral_of_strict_knownSimple
    (hb : 6 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (v : EdgePairedBackwardShift (h := h) p)
    (q : EdgePairedBackwardShift (h := h) v.path)
    (r : EdgePairedBackwardShift (h := h) q.path)
    (hstrict₀ : 4 < (Q d.radical v.start).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2))))
    (hstrict : 4 < (Q d.radical q.start).relIndex
      (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))) :
    ¬ ⁅Z d.radical r.start,Z d.radical (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  have hu := elementary_shifted_intermediate_central_radius_upper_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage p v q r hcentral hstrict₀ hstrict
  have hl := (elementary_intermediate_central_radius_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage v.path q r hcentral hstrict₀ hstrict).2.2.1
  omega

include e hz hn in
/-- Every elementary-image replacement of critical distance greater than four has
an actual critical path whose opposite radius index is exactly four.
The strict-radius theorem is now the only remaining source-(5.11) input
for this branch; no intermediate-centrality premise remains. -/
theorem elementary_four_lt_exists_radius_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    ∃ a a' : Vertex d.radical,
      ∃ _p : CriticalPath d.radical (replacementGeometry h d) a a',
        (Q d.radical a).relIndex (V d.radical a')=4 := by
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  by_cases hb6 : 6 < replacementDistance h d
  · obtain ⟨v⟩ := elementary_edge_paired_backward_shift_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage p
    obtain ⟨q,r,t,_,_,_,hact₄,hact₆⟩ := elementary_edge_paired_terminal_radius_actions_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hEimage v.path
    have small {c z : Vertex d.radical}
        (w : CriticalPath d.radical (replacementGeometry h d) c z)
        (hh : (Q d.radical c).relIndex (V d.radical z) ≤ 4) :
        (Q d.radical c).relIndex (V d.radical z)=4 :=
      (small_opposite_radius_eq_four_knownSimple (e := e) (hz := hz) (hn := hn)
        (by omega) w hh).2.2
    by_cases hv : 4 < (Q d.radical v.start).relIndex (V d.radical (p.walk.getVert (p.walk.length-2)))
    · by_cases hq : 4 < (Q d.radical q.start).relIndex
          (V d.radical (v.path.walk.getVert (v.path.walk.length-2)))
      · by_cases hr : 4 < (Q d.radical r.start).relIndex
            (V d.radical (q.path.walk.getVert (q.path.walk.length-2)))
        · have hn₄ := elementary_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hEimage p v q r hv hq
          have hn₆ := elementary_shifted_intermediate_noncentral_of_strict_knownSimple
            (e := e) (hz := hz) (hn := hn) hb6 hEimage v.path q r t hq hr
          let z₄ := q.path.walk.getVert (q.path.walk.length-2)
          have hi₄ : (Q d.radical q.start).relIndex (V d.radical z₄) ≤ 2 := by
            by_contra! hh
            exact hn₄ (hact₄ hh)
          have hi₆ : (Q d.radical r.start).relIndex (V d.radical z₄ ⊓ Q d.radical q.start) ≤ 2 := by
            by_contra! hh
            exact hn₆ (hact₆ hh)
          have hVQ : V d.radical z₄ ≤ Q d.radical z₄ :=
            V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color
              (by change 2 < replacementDistance h d; omega)
          let := finite_stabilizer d.radical z₄
          let : Finite (V d.radical z₄) := Finite.of_injective
            (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
          have htower := relIndex_inf_mul_relIndex (Q d.radical r.start)
            (Q d.radical q.start) (V d.radical z₄)
          rw [inf_comm (Q d.radical q.start)] at htower
          have hmono : (Q d.radical r.start).relIndex (V d.radical z₄) ≤
              (Q d.radical r.start ⊓ Q d.radical q.start).relIndex (V d.radical z₄) :=
            relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
          have hupper : (Q d.radical r.start).relIndex (V d.radical z₄) ≤ 4 := by
            rw [←htower] at hmono
            exact hmono.trans ((Nat.mul_le_mul hi₆ hi₄).trans (by decide))
          exact ⟨_,_,r.path,small r.path hupper⟩
        · exact ⟨_,_,r.path,small r.path (Nat.le_of_not_gt hr)⟩
      · exact ⟨_,_,q.path,small q.path (Nat.le_of_not_gt hq)⟩
    · exact ⟨_,_,v.path,small v.path (Nat.le_of_not_gt hv)⟩
  · have heven := replacementDistance_even h d
    rw [Nat.even_iff] at heven
    have heq : replacementDistance h d=6 := by omega
    obtain ⟨q,r,t,_,_,_,_,_,hi⟩ := elementary_edge_paired_terminal_six_knownSimple
      (e := e) (hz := hz) (hn := hn) heq hEimage p
    exact ⟨_,_,r.path,hi⟩

include e hz hn in
/-- Transport the forced radius-four path to the actual replacement base.
This is the remaining equality case for the strict-radius source argument. -/
theorem elementary_four_lt_exists_base_radius_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hEimage : IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d))) :
    ∃ a' : Vertex d.radical,
      ∃ _p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a',
        (Q d.radical (alpha d.radical)).relIndex (V d.radical a')=4 := by
  obtain ⟨a,a',p,hi⟩ := elementary_four_lt_exists_radius_four_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hEimage
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hex : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      (Q d.radical (act d.radical g⁻¹ a)).relIndex (V d.radical (act d.radical g⁻¹ a'))=4 := by
    refine ⟨p.act g⁻¹,?_⟩
    rw [Q_act,V_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hi
  rw [hbase] at hex
  exact ⟨_,hex⟩


end SylowTerminal
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
