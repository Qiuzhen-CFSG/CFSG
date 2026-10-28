module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalKernel

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# The central factor of the terminal restricted-kernel span

On three actual generating backward shifts, the opposite radius intersected
with the last edge seed is centralized by all three starting stabilizers.
Two generating edges give centrality at the intermediate and preceding
vertices. The retained component transporter then carries it to the last
critical start, fixing the intersection pointwise.

The restricted double-kernel commutator and the last critical line both lie
in this opposite radius, the last moved cover, and its common full kernel.
The checked common-kernel decomposition therefore splits their span as the
last critical line times its edge intersection. This intersection is exactly
the central part of the span, has order at most two, and has index two in
the span. It contributes no displacement under the whole last stabilizer.

If the preceding endpoint fails to normalize the restricted-kernel join,
the restricted commutator has order two and is also the full-omega kernel
commutator. Either it equals the last critical line, or the central part
is the entire moving central attachment at both transported starts.
The original-radical consumer constructs the shifts, retaining their literal
transporter, embedding and generating edge. Both moving covers are retained.

This proves the central-intersection and restricted-span comparisons used
in (5.10), not the terminal contradiction: propagation along the remaining
path, mover equality and containment, (5.11), image eight and distance-four
whole-core estimates remain with the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.10)--(5.11), printed pp.866--867,922--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalIntersection
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

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
theorem three_shift_radius_intersection_central
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let I := V d.radical z ⊓ Z d.radical t.edge
    I ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) ∧
    I ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) ∧
    I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let w := p.walk.getVert (p.walk.length-2)
  let I := V d.radical z ⊓ Z d.radical t.edge
  have hb2 : 2 < replacementDistance h d := by omega
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
  have hVQ : V d.radical z ≤ Q d.radical z :=
    V_le_Q d.radical (geometry := replacementGeometry h d) r.path.end_color hb2
  have hVQw : V d.radical z ≤ Q d.radical w := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) r.path.end_color
    rw [q.path.dist_end]
    have hl := q.path.length_eq_b
    change q.path.walk.length-(q.path.walk.length-2)+2 < replacementDistance h d
    omega
  have hCz : V d.radical z ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    hVQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z r.path.end_color)))
  have hCw : V d.radical z ≤ centralizer (Z d.radical w : Set (FreeAmalgam d.radical)) :=
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
private theorem three_shift_kernel_placements
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z d.radical t.start ⊓ Q d.radical v
    let F := Z d.radical z ⊓ Q d.radical r.start
    let H := ⁅K,F⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let W := Z d.radical t.start ⊓ centralizer
      (componentOrbit (Z d.radical v) (Q d.radical t.edge) : Set _)
    H ⊔ D ≤ V d.radical z ∧ H ⊔ D ≤ U d.radical t.start ∧ H ⊔ D ≤ W := by
  have hb2 : 2 < replacementDistance h d := by omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical r.start
  let H := ⁅K,F⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let W := Z d.radical t.start ⊓ centralizer
    (componentOrbit (Z d.radical v) (Q d.radical t.edge) : Set _)
  let J := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
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
      rw [(replacementGeometry h d).distance_constant z r.path.end_color,hzv]; exact hb2))
  have hDv : D ≤ Z d.radical v :=
    ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical v)
  have hDU : D ≤ U d.radical t.start :=
    (critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_left
  have hFcent : F ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    hFv.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical v t.path.end_color))).trans (centralizer_le hDv))
  have hfix := SylowTrappedMover.sixteen_common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path hsmall ht.2.2.2.2
  dsimp only at hfix
  rw [t.first] at hfix
  have hFJ : F ≤ J := (le_inf hFT hFcent).trans_eq hfix.1
  have hact := SylowTrappedMover.sixteen_small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path hsmall ht.2.2.2.2
  dsimp only at hact
  rw [t.first] at hact
  have hKW : ⁅K,J⁆ ≤ W := by
    have he : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1*x*1⁻¹ = x
      simp only [one_mul,inv_one,mul_one]
    have hh := (hact 1 (one_mem _)).2.2.1
    change ⁅K.map (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom,J⁆ ≤ W at hh
    rwa [he,Subgroup.map_id] at hh
  have hHW : H ≤ W := (commutator_mono le_rfl hFJ).trans hKW
  have hDcommon := SylowKernelDecomposition.sixteen_common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path hsmall ht.2.2.2.2
  dsimp only at hDcommon
  rw [t.first] at hDcommon
  have hDW : D ≤ W := (le_componentOrbit D (Q d.radical t.edge)).trans hDcommon.1
  have hKz : K ≤ stabilizer d.radical z := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical v z t.path.end_color (by rwa [SimpleGraph.dist_comm]))
  have hHz : H ≤ Z d.radical z := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (hKz.trans (Z_normalized d.radical z)))
  have hDV : D ≤ V d.radical z := hDv.trans
    (le_iSup_of_le v (le_iSup_of_le (by rw [SimpleGraph.dist_comm,hzv]) le_rfl))
  have hFU : F ≤ normalizer (U d.radical t.start : Set (FreeAmalgam d.radical)) :=
    (hFT.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift))).trans
      (U_normalized t.start)
  have hseedN : Z d.radical t.edge ≤ normalizer (U d.radical t.start : Set (FreeAmalgam d.radical)) :=
    ((adjacent_Z_le d.radical t.path.start_color t.adjacent_shift).trans
      (Z_le_stabilizer d.radical t.start)).trans (U_normalized t.start)
  have hseedF : Z d.radical t.edge ≤ centralizer (F : Set (FreeAmalgam d.radical)) :=
    (edge_seed_central htcol).trans (centralizer_le hFT)
  have hHU : H ≤ U d.radical t.start := by
    apply (commutator_mono inf_le_left le_rfl).trans
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d t.path.start_color t.adjacent_shift,
      commutator_sup_fixed _ _ F hseedN hseedF]
    exact le_normalizer_iff_commutator_le_left.mp hFU
  exact ⟨sup_le (hHz.trans (Z_le_VBall d.radical z 2)) hDV,sup_le hHU hDU,sup_le hHW hDW⟩

include e hz hn in
/-- The restricted kernel line and the last critical line generate the last
critical line times their common central attachment. That attachment is
central at all three starting vertices, and contributes no displacement
under the last whole stabilizer. No nonnormalization premise is needed. -/
theorem three_shift_kernel_central_decomposition_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    I ≤ U d.radical t.start ∧
    I ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) ∧
    I ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) ∧
    I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
    Nat.card I ≤ 2 ∧ H ⊔ D = D ⊔ I ∧
    H ≤ D ⊔ (U d.radical t.start ⊓ centralizer
      (stabilizer d.radical t.start : Set (FreeAmalgam d.radical))) ∧
    ∀ Y : Subgroup (FreeAmalgam d.radical), Y ≤ stabilizer d.radical t.start →
      ⁅H ⊔ D,Y⁆ = ⁅D,Y⁆ := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let I := (H ⊔ D) ⊓ Z d.radical t.edge
  let C := Z d.radical t.start ⊓ centralizer (Q d.radical t.edge : Set (FreeAmalgam d.radical))
  have hp := three_shift_kernel_placements (e := e) (hz := hz) (hn := hn) hb hcard p q r t
  have hc := three_shift_radius_intersection_central hb p q r t
  have hIrad : I ≤ V d.radical z ⊓ Z d.radical t.edge := inf_le_inf_right _ hp.1
  have hIr := hIrad.trans hc.1
  have hIq := hIrad.trans hc.2.1
  have hIt := hIrad.trans hc.2.2
  have hIU : I ≤ U d.radical t.start := inf_le_left.trans hp.2.1
  have hHZ : H ⊔ D ≤ Z d.radical t.start := hp.2.1.trans (DistanceEight.U_le_Z d.radical t.start)
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_shift
    rw [t.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
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
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hsmall : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp ht.2.2.2.2
  have hd := SylowKernelDecomposition.sixteen_line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path hsmall x hx hxm
  dsimp only at hd
  rw [t.first] at hd
  have hjoin : H ⊔ D ≤ D ⊔ C := hp.2.2.trans_eq hd.1
  have hDC : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    ((show C ≤ Z d.radical t.start from inf_le_left).trans
      ((le_centralizer (Z d.radical t.start)).trans (centralizer_le (show D ≤ Z d.radical t.start from le_sup_right.trans hHZ)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hdecomp : H ⊔ D = D ⊔ I := by
    apply le_antisymm _ (sup_le le_sup_right inf_le_left)
    intro x hx
    have hxprod : x ∈ (D : Set (FreeAmalgam d.radical)) * (C : Set (FreeAmalgam d.radical)) := by
      rw [←coe_mul_of_right_le_normalizer_left D C hDC]
      exact hjoin hx
    obtain ⟨a,ha,c,hc,hac⟩ := hxprod
    have hcjoin : c ∈ H ⊔ D := by
      have he : c = a⁻¹*x := by rw [←hac]; simp
      rw [he]
      exact (H ⊔ D).mul_mem ((H ⊔ D).inv_mem (Subgroup.mem_sup_right ha)) hx
    rw [←hac]
    exact (D ⊔ I).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hcjoin,hCedge hc⟩)
  have hIc : I ≤ U d.radical t.start ⊓ centralizer
      (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := le_inf hIU hIt
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hlayer := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let := finite_Z d.radical t.start
  let : Finite (U d.radical t.start ⊓ centralizer
      (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (inf_le_left.trans (DistanceEight.U_le_Z d.radical t.start)))
      (inclusion_injective _)
  have hcardI : Nat.card I ≤ 2 := (card_le_of_le hIc).trans
    (moving_central_attachment_card s hlayer t.path.start_color)
  refine ⟨hIU,hIr,hIq,hIt,hcardI,hdecomp,
    le_sup_left.trans (hdecomp.le.trans (sup_le_sup_left hIc D)),?_⟩
  intro Y hY
  rw [hdecomp]
  exact commutator_sup_fixed D I Y
    ((hIt.trans (centralizer_le (show D ≤ stabilizer d.radical t.start from
      (le_sup_right.trans hHZ).trans (Z_le_stabilizer d.radical t.start)))).trans
      (Subgroup.centralizer_le_normalizer _)) (hIt.trans (centralizer_le hY))

include e hz hn in
/-- The terminal edge intersection is exactly the central part of the
 two-line span. The last critical line is a disjoint complement of order
two, so the quotient by that central part has order exactly two. -/
theorem three_shift_kernel_central_factor_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    I = (H ⊔ D) ⊓ centralizer
      (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
    D ⊓ I = ⊥ ∧ I.relIndex (H ⊔ D) = 2 := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let I := (H ⊔ D) ⊓ Z d.radical t.edge
  have hp := three_shift_kernel_placements (e := e) (hz := hz) (hn := hn) hb hcard p q r t
  have hc := three_shift_kernel_central_decomposition_knownSimple hb hcard p q r t
  have hIt : I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := hc.2.2.2.1
  have hHZ : H ⊔ D ≤ Z d.radical t.start := hp.2.1.trans (DistanceEight.U_le_Z d.radical t.start)
  have htcol : color d.radical t.edge = true := by
    have hh := adjacent_color_ne d.radical t.adjacent_shift
    rw [t.path.start_color] at hh
    cases he : color d.radical t.edge
    · exact (hh he.symm).elim
    · rfl
  have hZQ : Z d.radical t.start ≤ Q d.radical t.start := Z_le_Q_of_dist_lt d.radical t.start
    ((replacementGeometry h d).exists_critical t.start t.path.start_color) (by
      rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ t.path.start_color]
      exact replacementDistance_pos h d)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
  have hIeq : I = (H ⊔ D) ⊓ centralizer
      (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm (le_inf inf_le_left hIt)
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [Z,if_neg (by simp [htcol])]
    refine mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h d.radical htcol t.adjacent_shift (hZQ (hHZ hx.1)),
      elemPow_eq_one_of_isElementaryAbelian x (hHZ hx.1),?_⟩
    intro y hy
    exact hx.2 y (hy.2 _ (adjacent_symm d.radical t.adjacent_shift))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hlayer := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hsmall : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have hDI : D ⊓ I = ⊥ := le_bot_iff.mp
    ((inf_le_inf_left D hIt).trans_eq (small_critical_commutator_inf_centralizer s hlayer t.path hsmall))
  have hIN : I ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (hIt.trans (centralizer_le (show D ≤ stabilizer d.radical t.start from
      (le_sup_right.trans hHZ).trans (Z_le_stabilizer d.radical t.start)))).trans
        (Subgroup.centralizer_le_normalizer _)
  let := finite_Z d.radical t.start
  let : Finite I := Finite.of_injective (inclusion (inf_le_left.trans hHZ)) (inclusion_injective _)
  have hindex : I.relIndex (H ⊔ D) = 2 := by
    rw [hc.2.2.2.2.2.1,relIndex_sup_of_normalizes D I hIN,←inf_relIndex_right,inf_comm,hDI]
    simpa using ht.2.2.2.1
  exact ⟨hIeq,hDI,hindex⟩

include e hz hn in
/-- In the nonnormalizing branch, either the restricted commutator is the
last critical line, or its span with that line contains the entire moving
central attachment at both transported starts. The full omega kernel has
exactly the same restricted commutator. -/
theorem three_shift_nonnormalized_central_alternative_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z d.radical t.start ⊓ Q d.radical v
    let H := ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    Nat.card H = 2 ∧
    ⁅K,X d.radical z ⊓ Q d.radical r.start⁆ = H ∧
    (H = D ∨
      (I = U d.radical t.start ⊓ centralizer
        (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
      I = U d.radical q.start ⊓ centralizer
        (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) ∧ Nat.card I = 2)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let H := ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let I := (H ⊔ D) ⊓ Z d.radical t.edge
  let At := U d.radical t.start ⊓ centralizer
    (stabilizer d.radical t.start : Set (FreeAmalgam d.radical))
  let Aq := U d.radical q.start ⊓ centralizer
    (stabilizer d.radical q.start : Set (FreeAmalgam d.radical))
  have hker := (SylowTerminalKernel.three_shift_kernel_control_knownSimple hb hcard p q r t).2.2.2.2.2 hnorm
  have hfull := SylowTerminalKernel.three_shift_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hnorm
  have hc := three_shift_kernel_central_decomposition_knownSimple hb hcard p q r t
  have hp := three_shift_kernel_placements (e := e) (hz := hz) (hn := hn) hb hcard p q r t
  have hIt : I ≤ At := le_inf hc.1 hc.2.2.2.1
  have hIq : I ≤ Aq := by
    refine le_inf ?_ hc.2.2.1
    have hr2 : r.path.walk.getVert 2 = q.start := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
    have hshift : act d.radical t.transporter q.start = t.start := by simpa only [hr2] using t.start_eq
    have hback : act d.radical t.transporter⁻¹ t.start = q.start := by
      rw [←hshift,←act_mul,mul_inv_cancel,act_one]
    have hu := U_act d.radical t.transporter⁻¹ t.start
    rw [inv_inv,hback] at hu
    have hh := map_mono (f := (MulAut.conj t.transporter).toMonoidHom) hc.1
    rw [fixed_map I (stabilizer d.radical r.start) hc.2.1 t.transporter_mem] at hh
    exact hh.trans_eq hu.symm
  refine ⟨hker.1,(hfull.2.2 K inf_le_right).1,?_⟩
  by_cases he : H = D
  · exact Or.inl he
  apply Or.inr
  let := finite_Z d.radical t.start
  let := finite_Z d.radical q.start
  let : Finite I := Finite.of_injective
    (inclusion ((inf_le_left.trans hp.2.1).trans (DistanceEight.U_le_Z d.radical t.start)))
    (inclusion_injective _)
  let : Finite D := Finite.of_injective
    (inclusion ((le_sup_right.trans hp.2.1).trans (DistanceEight.U_le_Z d.radical t.start)))
    (inclusion_injective _)
  let : Finite At := Finite.of_injective
    (inclusion (inf_le_left.trans (DistanceEight.U_le_Z d.radical t.start))) (inclusion_injective _)
  let : Finite Aq := Finite.of_injective
    (inclusion (inf_le_left.trans (DistanceEight.U_le_Z d.radical q.start))) (inclusion_injective _)
  have hnI : I ≠ ⊥ := by
    intro hzero
    have hj : H ⊔ D = D := by
      have hj : H ⊔ D = D ⊔ I := hc.2.2.2.2.2.1
      rwa [hzero,sup_bot_eq] at hj
    have hle : H ≤ D := le_sup_left.trans hj.le
    have hd := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
      (e := e) (hz := hz) (hn := hn) hb q.path r t
    exact he (eq_of_le_of_card_ge hle (by rw [hker.1,hd.2.2.2.1]))
  have hi : Nat.card I = 2 := by
    have hpos := (one_lt_card_iff_ne_bot I).mpr hnI
    have hbound : Nat.card I ≤ 2 := hc.2.2.2.2.1
    omega
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hlayer := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hAt : Nat.card At ≤ 2 := moving_central_attachment_card s hlayer t.path.start_color
  have hAq : Nat.card Aq ≤ 2 := moving_central_attachment_card s hlayer q.path.start_color
  exact ⟨eq_of_le_of_card_ge hIt (hAt.trans_eq hi.symm),eq_of_le_of_card_ge hIq (hAq.trans_eq hi.symm),hi⟩

/-- The original MS radical, with its literal embedding and transporter,
supplies the terminal central decomposition and its exact index. This
discharges the central-intersection and restricted-span calculations of
(5.10); neither central generation nor a normalization choice is supplied
by the caller. -/
theorem original_radical_three_shift_central_factor_knownSimple
    (hb : 4 < replacementDistance h d)
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
      let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
      let D := ⁅Z d.radical t.start,Z d.radical v⁆
      let I := (H ⊔ D) ⊓ Z d.radical t.edge
      I ≤ U d.radical t.start ∧
      I ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) ∧
      I ≤ centralizer (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) ∧
      I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
      Nat.card I ≤ 2 ∧ H ⊔ D = D ⊔ I ∧
      I = (H ⊔ D) ⊓ centralizer
        (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
      D ⊓ I = ⊥ ∧ I.relIndex (H ⊔ D) = 2 ∧
      H ≤ D ⊔ (U d.radical t.start ⊓ centralizer
        (stabilizer d.radical t.start : Set (FreeAmalgam d.radical))) ∧
      (∀ Y : Subgroup (FreeAmalgam d.radical), Y ≤ stabilizer d.radical t.start →
        ⁅H ⊔ D,Y⁆ = ⁅D,Y⁆) ∧
      ((¬ Z d.radical z ≤ normalizer
        (((Z d.radical t.start ⊓ Q d.radical v) ⊔ Z d.radical r.start :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) →
        Nat.card H = 2 ∧
        ⁅Z d.radical t.start ⊓ Q d.radical v,X d.radical z ⊓ Q d.radical r.start⁆ = H ∧
        (H = D ∨ (I = U d.radical t.start ⊓ centralizer
          (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
        I = U d.radical q.start ⊓ centralizer
          (stabilizer d.radical q.start : Set (FreeAmalgam d.radical)) ∧ Nat.card I = 2))) := by
  obtain ⟨q,hqe,hqT,hqgen⟩ := SylowShiftChain.original_radical_backward_shift_knownSimple
    hb hcard p hfirst
  obtain ⟨r,hre⟩ := SylowShiftChain.backwardShift_with_edge hb hcard q.path
  obtain ⟨t,hte⟩ := SylowShiftChain.backwardShift_with_edge hb hcard r.path
  have hc := three_shift_kernel_central_decomposition_knownSimple hb hcard p q r t
  have hf := three_shift_kernel_central_factor_knownSimple hb hcard p q r t
  refine ⟨q,r,t,hqe,hqT,hqgen,hre,hte,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,
    hc.2.2.2.2.1,hc.2.2.2.2.2.1,hf.1,hf.2.1,hf.2.2,
    hc.2.2.2.2.2.2.1,hc.2.2.2.2.2.2.2,?_⟩
  exact three_shift_nonnormalized_central_alternative_knownSimple hb hcard p q r t

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalIntersection
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
