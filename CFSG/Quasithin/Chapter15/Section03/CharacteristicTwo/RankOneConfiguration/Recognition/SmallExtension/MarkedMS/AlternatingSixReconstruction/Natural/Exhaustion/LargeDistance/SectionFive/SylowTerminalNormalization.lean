module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Terminal normalization and whole-core containment above distance six

For three actual generating backward shifts, the last predecessor radius
meets the last edge seed in a subgroup centralized by all three starting
stabilizers. This uses distance greater than six to centralize both endpoint
seeds in the two generation equations.

The whole last seed's commutator with the reverse critical kernel lies both
in this predecessor radius and in the common kernel of the last critical
pair. The common-kernel decomposition bounds it by the last critical line
times the full central attachment. SylowTerminalActor then forces the
restricted double-kernel commutator to vanish, eliminating the nonnormalizing
alternative. The full endpoint omega subgroup also normalizes the same join:
its central-generation alternative adds only a pointwise centralizing factor.
The earlier source dichotomy now places the whole intermediate core inside
the last actual small mover.

The final application constructs the shifts from the original restricted
radical, with its exact transporter and generating edge. Both moved covers
and all central attachments are retained. Distance six, the subsequent
mover comparison and (5.11), image eight, and distance-four whole-core
estimates remain with the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10), printed pp.922--923; the separate b=6 paragraph is not used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
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


namespace SylowTerminalNormalization

omit [Finite G] in
private theorem edge_seed_central {t : Vertex d.radical} (ht : color d.radical t = true) :
    Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
  intro x hx
  rw [Z,if_neg (by simp [ht])] at hx
  exact (mem_omegaCenter_iff.mp hx).2.2

omit [Finite G] in
private theorem fixed_map (A H : Subgroup (FreeAmalgam d.radical))
    (hc : A ≤ centralizer (H : Set (FreeAmalgam d.radical)))
    {x : FreeAmalgam d.radical} (hx : x ∈ H) :
    A.map (MulAut.conj x).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hc hx))

/-- Two generating edges and the same shift transporter make the opposite
radius's edge intersection central at all three starting vertices. -/
private theorem predecessor_radius_intersection_central
    (hb : 6 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let I := V d.radical v ⊓ Z d.radical t.edge
    I ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) ∧
    I ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) ∧
    I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let w := p.walk.getVert (p.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let I := V d.radical v ⊓ Z d.radical t.edge
  have htz : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
  have hrz : color d.radical r.edge = true := by
    have hh := adjacent_color_ne d.radical r.adjacent_start
    rw [q.path.start_color] at hh
    cases he : color d.radical r.edge
    · exact (hh he.symm).elim
    · rfl
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hzw : (cosetGraph d.radical).dist z w = 2 := by
    rw [q.path.dist_end]
    have hl : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
    omega
  have hvw : (cosetGraph d.radical).dist v w ≤ 4 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := v) (v := z) (w := w)
    omega
  have hVQz : V d.radical v ≤ Q d.radical z := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) t.path.end_color
    change (cosetGraph d.radical).dist v z + 2 < replacementDistance h d
    rw [hvz]
    omega
  have hVQw : V d.radical v ≤ Q d.radical w := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) t.path.end_color
    change (cosetGraph d.radical).dist v w + 2 < replacementDistance h d
    omega
  have hCz : V d.radical v ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    hVQz.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z r.path.end_color)))
  have hCw : V d.radical v ≤ centralizer (Z d.radical w : Set (FreeAmalgam d.radical)) :=
    hVQw.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical w q.path.end_color)))
  have hIr : I ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←t.generation]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (edge_seed_central htz)))
      (le_centralizer_iff.mp (inf_le_left.trans hCz))
  have hIedge : I ≤ Z d.radical r.edge := by
    obtain ⟨x,hx,hxe⟩ := stabilizer_transitive_neighbors d.radical r.start
      t.adjacent_start r.adjacent_shift
    rw [←hxe,Z_act,←fixed_map I (stabilizer d.radical r.start) hIr
      ((stabilizer d.radical r.start).inv_mem hx)]
    exact map_mono inf_le_right
  have hIq : I ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←r.generation]
    exact sup_le (le_centralizer_iff.mp (hIedge.trans (edge_seed_central hrz)))
      (le_centralizer_iff.mp (inf_le_left.trans hCw))
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hshift : act d.radical t.transporter q.start = t.start := by
    simpa only [hr2] using t.start_eq
  have hIt : I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := by
    rw [←hshift,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj t.transporter⁻¹).toMonoidHom) hIq).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [fixed_map I (stabilizer d.radical r.start) hIr
      ((stabilizer d.radical r.start).inv_mem t.transporter_mem)] at hh
  exact ⟨hIr,hIq,hIt⟩

include e hz hn in
/-- Above distance six, the whole terminal seed commutator, with its full
reverse kernel, lies in the last critical line times the central attachment. -/
theorem whole_seed_commutator_aligned_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z d.radical t.start,Z d.radical z ⊓ Q d.radical r.start⁆ ≤
      ⁅Z d.radical t.start,Z d.radical v⁆ ⊔
        (U d.radical t.start ⊓ centralizer
          (stabilizer d.radical t.start : Set (FreeAmalgam d.radical))) := by
  have hb4 : 4 < replacementDistance h d := by omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let F := Z d.radical z ⊓ Q d.radical r.start
  let J := ⁅Z d.radical t.start,F⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let W := Z d.radical t.start ⊓ centralizer
    (componentOrbit (Z d.radical v) (Q d.radical t.edge) : Set _)
  let C := Z d.radical t.start ⊓ centralizer (Q d.radical t.edge : Set (FreeAmalgam d.radical))
  let I := (J ⊔ D) ⊓ Z d.radical t.edge
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 q.path r t
  have hsmall : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
  have hzv : (cosetGraph d.radical).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hFT : F ≤ Q d.radical t.edge := inf_le_right.trans
    (Q_le_adjacent_h d.radical htcol t.adjacent_start)
  have hFv : F ≤ Q d.radical v := inf_le_left.trans (Z_le_Q_of_dist_lt d.radical z
    ((replacementGeometry h d).exists_critical z r.path.end_color) (by
      rw [(replacementGeometry h d).distance_constant z r.path.end_color,hzv]
      exact (show 2 < replacementDistance h d by omega)))
  have hFV : F ≤ V d.radical v := inf_le_left.trans
    ((Z_le_localZSpan d.radical z v).trans (localZSpan_le_V d.radical hzv.le))
  have hZtv : Z d.radical t.start ≤ stabilizer d.radical v :=
    Z_le_stabilizer_of_dist_le t.start _ t.path.critical.1.le
  have hJV : J ≤ V d.radical v := (commutator_mono le_rfl hFV).trans
    (le_normalizer_iff_commutator_le_right.mp (hZtv.trans (V_normalized v)))
  have hDv : D ≤ Z d.radical v :=
    ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical v)
  have hDV : D ≤ V d.radical v := hDv.trans (Z_le_VBall d.radical v 2)
  have hDU : D ≤ U d.radical t.start :=
    (critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_left
  have hFU : F ≤ normalizer (U d.radical t.start : Set (FreeAmalgam d.radical)) :=
    (hFT.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))).trans
      (U_normalized t.start)
  have hseedN : Z d.radical t.edge ≤ normalizer (U d.radical t.start : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical t.path.start_color t.adjacent_shift).trans
      (Z_le_stabilizer d.radical t.start)).trans (U_normalized t.start)
  have hJU : J ≤ U d.radical t.start := by
    dsimp only [J]
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d t.path.start_color t.adjacent_shift,
      commutator_sup_fixed _ _ F hseedN ((edge_seed_central htcol).trans (centralizer_le hFT))]
    exact le_normalizer_iff_commutator_le_left.mp hFU
  have hop := SylowTrappedMover.sixteen_opposite_core_full_kernel_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hcard t.path hsmall ht.2.2.2.2
  dsimp only at hop
  rw [t.first] at hop
  have hJW : J ≤ W := (commutator_mono le_rfl (le_inf hFT hFv)).trans hop.2.2.1
  have hDcommon := SylowKernelDecomposition.sixteen_common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hcard t.path hsmall ht.2.2.2.2
  dsimp only at hDcommon
  rw [t.first] at hDcommon
  have hDW : D ≤ W := (le_componentOrbit D (Q d.radical t.edge)).trans hDcommon.1
  have hcent := predecessor_radius_intersection_central hb p q r t
  have hIt : I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) :=
    (inf_le_inf_right _ (sup_le hJV hDV)).trans hcent.2.2
  have hIU : I ≤ U d.radical t.start := inf_le_left.trans (sup_le hJU hDU)
  have hZQ : Z d.radical t.start ≤ Q d.radical t.start := Z_le_Q_of_dist_lt d.radical t.start
    ((replacementGeometry h d).exists_critical t.start t.path.start_color) (by
      rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ t.path.start_color]
      exact replacementDistance_pos h d)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
  have hCedge : C ≤ Z d.radical t.edge := by
    intro x hx
    rw [Z,if_neg (by simp [htcol])]
    exact mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical htcol t.adjacent_shift (hZQ hx.1),
      elemPow_eq_one_of_isElementaryAbelian x hx.1,hx.2⟩
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp ht.2.2.2.2
  have hd := SylowKernelDecomposition.sixteen_line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 hcard t.path hsmall x hx hxm
  dsimp only at hd
  rw [t.first] at hd
  have hjoin : J ⊔ D ≤ D ⊔ C := (sup_le hJW hDW).trans_eq hd.1
  have hDC : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (inf_le_left.trans ((le_centralizer (Z d.radical t.start)).trans
      (centralizer_le (hDU.trans (DistanceEight.U_le_Z d.radical t.start))))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hdecomp : J ⊔ D ≤ D ⊔ I := by
    intro x hx
    have hxprod : x ∈ (D : Set (FreeAmalgam d.radical)) * (C : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left D C hDC]
      exact hjoin hx
    obtain ⟨a,ha,c,hc,hac⟩ := hxprod
    have hcjoin : c ∈ J ⊔ D := by
      have he : c = a⁻¹*x := by rw [←hac]; simp
      rw [he]
      exact (J ⊔ D).mul_mem ((J ⊔ D).inv_mem (Subgroup.mem_sup_right ha)) hx
    rw [←hac]
    exact (D ⊔ I).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hcjoin,hCedge hc⟩)
  exact le_sup_left.trans (hdecomp.trans (sup_le_sup_left (le_inf hIU hIt) D))

include e hz hn in
/-- The terminal nonnormalizing alternative is impossible above distance six.
The whole-seed estimate forces the restricted double-kernel commutator to
vanish, contrary to its required order two in that alternative. -/
theorem three_shift_normalization_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z d.radical t.start ⊓ Q d.radical v
    let F := Z d.radical z ⊓ Q d.radical r.start
    ⁅K,F⁆ = ⊥ ∧ Z d.radical z ≤ normalizer
      ((K ⊔ Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb4 : 4 < replacementDistance h d := by omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical r.start
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 q.path r t
  have hsmall : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
  have hFG : F ≤ stabilizer d.radical t.start :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))
  have hzero : ⁅K,F⁆ = ⊥ := (small_critical_actor_le_of_line_mod_center s hc t.path hsmall F hFG
    (whole_seed_commutator_aligned_knownSimple hb hcard p q r t)).2
  refine ⟨hzero,?_⟩
  by_contra hn
  have hline := (SylowTerminalKernel.three_shift_kernel_control_knownSimple
    hb4 hcard p q r t).2.2.2.2.2 hn
  have hcardH : Nat.card (⁅K,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := hline.1
  rw [hzero,Subgroup.card_bot] at hcardH
  omega

include e hz hn in
/-- Normalization also holds for the full endpoint omega subgroup appearing
in the source. Its central-generation alternative contributes only a factor
centralizing the literal restricted-kernel join. -/
theorem three_shift_full_omega_normalization_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    X d.radical z ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical v) ⊔ Z d.radical r.start :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hb4 : 4 < replacementDistance h d := by omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let N := K ⊔ Z d.radical r.start
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hd := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 p q r
  have hsmall : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by rw [hd.2.1]; decide
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
  have hzv : (cosetGraph d.radical).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hXG : X d.radical z ⊓ Q d.radical r.start ≤ stabilizer d.radical t.start :=
    (inf_le_right.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))
  have hXv : X d.radical z ⊓ Q d.radical r.start ≤ stabilizer d.radical v :=
    ((inf_le_left.trans (omegaCenter_le (Q d.radical z))).trans
      (Q_le_stabilizer_of_dist_two d.radical z v r.path.end_color hzv))
  have hNK : X d.radical z ⊓ Q d.radical r.start ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (le_inf (hXG.trans (Z_normalized d.radical t.start))
      (hXv.trans (Q_normalized d.radical v))).trans inf_normalizer_le_normalizer_inf
  have hKQ : K ≤ Q d.radical r.start :=
    (inf_le_left.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q (by omega : 2 < replacementDistance h d) r.start r.path.start_color)
  have hvG : Q d.radical v ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical v z t.path.end_color
      (SimpleGraph.dist_comm.trans hzv)
  rcases critical_X_generation_or_normalization s hc r.path hsmall K
    (inf_le_right.trans hvG) hKQ hNK with hgen | hnorm
  · have hNG : N ≤ stabilizer d.radical z := sup_le (inf_le_right.trans hvG)
      (Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le)
    change X d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical))
    change X d.radical z = _ at hgen
    rw [hgen]
    exact sup_le ((DistanceEight.U_le_Z d.radical z).trans
      (three_shift_normalization_knownSimple hb hcard p q r t).2)
      ((inf_le_right.trans (centralizer_le hNG)).trans (Subgroup.centralizer_le_normalizer _))
  · exact hnorm

include e hz hn in
/-- The intermediate whole core is contained in the actual last small mover.
The normalization premise from the earlier terminal dichotomy is discharged. -/
theorem three_shift_core_containment_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    Q d.radical r.start ≤
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4 := by
  have hn := (three_shift_normalization_knownSimple hb hcard p q r t).2
  exact ((SylowTerminalKernel.three_shift_kernel_control_knownSimple
    (by omega : 4 < replacementDistance h d) hcard p q r t).2.2.2.2.1 hn).1

/-- The literal original radical supplies a generating shift with its exact
transporter. Above distance six its third shift has trivial restricted
kernel commutator, endpoint normalization and containment of the whole
intermediate core in the last small mover. Both covers and the original
restricted radical remain unchanged. -/
theorem original_radical_terminal_normalization_knownSimple
    (hb : 6 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
      (t : BackwardShift (h := h) r.path),
      act d.radical q.transporter (beta d.radical) = q.edge ∧
      T.map (MulAut.conj q.transporter⁻¹).toMonoidHom = Q d.radical q.edge ∧
      T.map (MulAut.conj q.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      act d.radical r.transporter (q.path.walk.getVert 1) = r.edge ∧
      act d.radical t.transporter (r.path.walk.getVert 1) = t.edge ∧
      let z := q.path.walk.getVert (q.path.walk.length-2)
      let v := r.path.walk.getVert (r.path.walk.length-2)
      let K := Z d.radical t.start ⊓ Q d.radical v
      ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ = ⊥ ∧
      Z d.radical z ≤ normalizer
        ((K ⊔ Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      X d.radical z ≤ normalizer
        ((K ⊔ Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      Q d.radical r.start ≤
        SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4 := by
  have hb4 : 4 < replacementDistance h d := by omega
  obtain ⟨q,hqe,hqT,hqgen⟩ := SylowShiftChain.original_radical_backward_shift_knownSimple
    hb4 hcard p hfirst
  obtain ⟨r,hr⟩ := SylowShiftChain.backwardShift_with_edge hb4 hcard q.path
  obtain ⟨t,ht⟩ := SylowShiftChain.backwardShift_with_edge hb4 hcard r.path
  have hn := three_shift_normalization_knownSimple hb hcard p q r t
  exact ⟨q,r,t,hqe,hqT,hqgen,hr,ht,hn.1,hn.2,
    three_shift_full_omega_normalization_knownSimple hb hcard p q r t,
    three_shift_core_containment_knownSimple hb hcard p q r t⟩

end SylowTerminalNormalization

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
