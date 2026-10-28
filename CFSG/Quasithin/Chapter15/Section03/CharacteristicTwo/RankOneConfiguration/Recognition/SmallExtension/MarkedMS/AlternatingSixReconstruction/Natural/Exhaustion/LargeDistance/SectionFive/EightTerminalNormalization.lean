module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightTerminalKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalNormalization
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalSix
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel

/-!
# Whole-kernel normalization at every distance above four

For distance six, the natural cover has no moving central attachment. On
the augmentation cover, an actor centralizing a transposition cannot move
its fixed hyperplane into that transposition's own line. These facts exclude
the coincident-line alternative supplied by EightTerminalKernel.

Above distance six, the entire terminal seed's movement under the reverse
kernel lies in the last critical line times the central attachment. The
faithful natural quotient then forces the restricted commutator to vanish.
Thus the full endpoint omega subgroup normalizes the same restricted-kernel
join in both cases, and the actual whole neighboring core lies in the last
edge mover. No selected-span estimate is substituted for this containment.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.10), printed pp.866--867,922--923. The cover calculation
and geometric transport are reused from the natural image-sixteen proof;
all mover and critical-kernel estimates use the actual image-eight edge.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace EightTerminal
open SylowTerminalPath
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem three_shift_nonnormalized_lines_distinct_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆ ≠
      ⁅Z d.radical t.start,Z d.radical v⁆ := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let F := Z d.radical z ⊓ Q d.radical r.start
  change ⁅Z d.radical t.start ⊓ Q d.radical v,F⁆ ≠ ⁅Z d.radical t.start,Z d.radical v⁆
  intro heq
  have hattach := three_shift_nonnormalized_attachment_escape_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hnorm
  have hc32 : Nat.card (replacementMoved d)=32 := by
    rcases moved_card s with h16|h32
    · have hz := moving_attachment_zero_of_sixteen s hc h16 r.path.end_color
      exact (hattach (hz ▸ bot_le)).elim
    · exact h32
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hsmall : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have htcol : color d.radical t.edge=true := by
    have hh := adjacent_color_ne d.radical t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color d.radical t.edge <;> simp_all
  have hAt : Z d.radical v ≤ Q d.radical t.edge := by
    rw [←t.first]
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v t.path.end_color)
    rw [SimpleGraph.dist_comm,t.path.dist_end,(replacementGeometry h d).distance_constant _ t.path.end_color]
    have hl : t.path.walk.length=replacementDistance h d := t.path.length_eq_b
    change t.path.walk.length-1 < replacementDistance h d
    omega
  have hFt : F ≤ Q d.radical t.edge := inf_le_right.trans (Q_le_adjacent_h d.radical htcol t.adjacent_start)
  have hFv : F ≤ Q d.radical v := by
    apply inf_le_left.trans
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z r.path.end_color)
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color,SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length=replacementDistance h d := r.path.length_eq_b
    change r.path.walk.length-(r.path.walk.length-2) < replacementDistance h d
    omega
  have hzero := critical_fixed_line_zero_of_cover32 s hc hc32 t.path hsmall
    t.adjacent_shift hAt F hFt hFv heq.le
  have hn := critical_Z_commutator_ne_bot s hc t.path
  exact hn (heq.symm.trans hzero)

include e hz hn in
private theorem six_terminal_normalization_knownSimple
    (hb : replacementDistance h d = 6)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  by_contra hfail
  exact three_shift_nonnormalized_lines_distinct_knownSimple (e := e) (hz := hz) (hn := hn) (by omega) p q r t hfail
    (six_nonnormalized_coincident_lines_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr hfail).1

include e hz hn in
private theorem whole_seed_commutator_aligned_knownSimple
    (hb : 6 < replacementDistance h d)
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
      commutator_sup_fixed _ _ F hseedN ((SylowTerminalNormalization.edge_seed_central htcol).trans (centralizer_le hFT))]
    exact le_normalizer_iff_commutator_le_left.mp hFU
  have hop := EightTrappedKernel.opposite_core_full_kernel_control_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 t.path hsmall ht.2.2.2.2
  dsimp only at hop
  rw [t.first] at hop
  have hJW : J ≤ W := (commutator_mono le_rfl (le_inf hFT hFv)).trans hop.2.2.1
  have hDcommon := EightBackwardKernel.common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 t.path hsmall ht.2.2.2.2
  dsimp only at hDcommon
  rw [t.first] at hDcommon
  have hDW : D ≤ W := (le_componentOrbit D (Q d.radical t.edge)).trans hDcommon.1
  have hcent := SylowTerminalNormalization.predecessor_radius_intersection_central hb p q r t
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
  have hd := EightBackwardKernel.line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb4 t.path hsmall x hx hxm
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
private theorem three_shift_normalization_knownSimple
    (hb : 6 < replacementDistance h d)
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
    (whole_seed_commutator_aligned_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t)).2
  refine ⟨hzero,?_⟩
  by_contra hfail
  have hline := (three_shift_kernel_control_knownSimple (e := e) (hz := hz) (hn := hn)
    hb4 p q r t).2.2.2.2.2 hfail
  have hcardH : Nat.card (⁅K,F⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := hline.1
  rw [hzero,Subgroup.card_bot] at hcardH
  omega

include e hz hn in
private theorem orbit_terminal_normalization_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  by_cases h6 : replacementDistance h d=6
  · exact six_terminal_normalization_knownSimple (e := e) (hz := hz) (hn := hn) h6 p q r t hr
  · have he := replacementDistance_even h d
    rw [Nat.even_iff] at he
    exact (three_shift_normalization_knownSimple (e := e) (hz := hz) (hn := hn)
      (by omega) p q r t).2

include e hz hn in
/-- The entire endpoint omega subgroup normalizes the literal restricted-kernel join, including distance six and both moved covers. -/
theorem orbit_terminal_full_omega_normalization_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    X d.radical z ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical v) ⊔ Z d.radical r.start :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let N := K ⊔ Z d.radical r.start
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hd := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
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
      (orbit_terminal_normalization_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr))
      ((inf_le_right.trans (centralizer_le hNG)).trans (Subgroup.centralizer_le_normalizer _))
  · exact hnorm

include e hz hn in
/-- The whole intermediate core lies in the last actual edge mover on an orbit-complete path. -/
theorem orbit_terminal_core_containment_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    Q d.radical r.start ≤
      SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4 := by
  exact ((three_shift_kernel_control_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t).2.2.2.2.1
    (orbit_terminal_normalization_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr)).1

end EightTerminal
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
