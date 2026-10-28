module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightChain
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightUnequalCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalSix
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowUnequalResidual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalIntersection
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeFullKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion

/-!
# Terminal kernels for the actual image-eight edge

The small mover has index two in the actual edge core. If it omits the
neighboring component core, it generates the component residual with the
same opposite seed. The strict forward slice excludes that generation when
both actors normalize the restricted-kernel join. This gives whole-core
containment in the normalizing branch, and a nonzero restricted commutator
line in the other branch.

The restricted line and the last critical line span their last critical
line times the full central attachment. The attachment is fixed by all
three starting stabilizers and propagates along the constructed orbit path.
At distance six, a nonnormalizing branch therefore has coincident lines.
The calculations adapt the image-sixteen terminal argument to the smaller
actual edge mover, using EightTrappedKernel throughout. They do not identify
this mover with the larger relative-normalizer mover or discard the central
attachment of the order-thirty-two cover.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.9)--(5.10), printed pp.917,921--923. Generic geometric
and group lemmas are reused from the existing natural replacement proof.
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
private theorem opposite_residual_of_core_not_le_knownSimple
    (hb : 4 < replacementDistance h d)
    {a c t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical t ⊔ A = stabilizer d.radical a)
    (hnot : ¬ Q d.radical a ≤ SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4) :
    let E := SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4
    (E ⊔ A).relIndex (stabilizer d.radical a) ≤ 2 ∧ Ltilde d.radical a ≤ E ⊔ A := by
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases he : color d.radical t <;> simp_all
  have hc : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  obtain ⟨_,_,_,hET,_,hEi,_⟩ := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hc hct
  let := finite_stabilizer d.radical a
  exact SectionFive.index_two_opposite_generation (stabilizer d.radical a) (Q d.radical a) (Q d.radical t)
    (SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4) A
    (Q_le_adjacent_h d.radical ht hat)
    (fun _ hx => hx.2 _ (adjacent_symm d.radical hat)) hET (Q_normalized d.radical a)
    hEi hnot hgen

include e hz hn in
/-- The actual index-two edge mover controls the full restricted kernel. Terminal normalization places the whole neighboring core in that mover. -/
theorem three_shift_kernel_control_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z d.radical t.start ⊓ Q d.radical v
    let N := K ⊔ Z d.radical r.start
    let E := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4
    K.relIndex (Z d.radical t.start) = 2 ∧
      (¬ K ≤ B d.radical r.start ((replacementGeometry h d).Z_normal _)) ∧
      E ≤ normalizer (N : Set (FreeAmalgam d.radical)) ∧
      (¬ Ltilde d.radical r.start ≤ normalizer (N : Set (FreeAmalgam d.radical))) ∧
      (Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical)) →
        Q d.radical r.start ≤ E ∧
        (X d.radical r.start = U d.radical r.start ⊔
          (X d.radical r.start ⊓ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical))) →
          E = SmallMover.join (U d.radical r.start) (Q d.radical r.start) (Q d.radical t.edge) 4)) ∧
      ((¬ Z d.radical z ≤ normalizer (N : Set (FreeAmalgam d.radical))) →
        let H := ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆
        Nat.card H = 2 ∧ H ≤ K ∧
          H ≤ ⁅Z d.radical r.start,Z d.radical z⁆ ⊔
            (Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)))) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let N := K ⊔ Z d.radical r.start
  let E := SmallMover.join (U d.radical t.start) (Q d.radical t.start) (Q d.radical t.edge) 4
  have hr := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hrs : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by rw [hr.2.1]; decide
  have hts : (Q d.radical v).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have hki : K.relIndex (Z d.radical t.start) = 2 := by
    rw [show K = Z d.radical t.start ⊓ Q d.radical v from rfl,inf_relIndex_left]
    exact ht.2.1
  have hstrict : 2 < (B d.radical r.start ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical t.start) := by
    have hh := EightBaumann.small_forward_slice_strict_knownSimple
      (e := e) (hz := hz) (hn := hn) hb r.path hrs
    have hm : (B d.radical r.start ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj t.transporter⁻¹).toMonoidHom =
          B d.radical r.start ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        (geometry := replacementGeometry h d) hb2 r.start r.path.start_color
        ((stabilizer d.radical r.start).inv_mem t.transporter_mem))
    rw [←t.start_eq,U_act,←hm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hh
  let := finite_Z d.radical t.start
  have hnot : ¬ K ≤ B d.radical r.start ((replacementGeometry h d).Z_normal _) := by
    intro hKB
    have hi : (B d.radical r.start ((replacementGeometry h d).Z_normal _)).relIndex
        (Z d.radical t.start) ≤ 2 :=
      (relIndex_le_of_le_left hKB index_ne_zero_of_finite).trans_eq hki
    have hj := relIndex_le_of_le_right (H := B d.radical r.start ((replacementGeometry h d).Z_normal _))
      (DistanceEight.U_le_Z d.radical t.start) index_ne_zero_of_finite
    exact (Nat.not_le_of_gt hstrict) (hj.trans hi)
  have hfix := EightTrappedKernel.common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path hts ht.2.2.2.2
  dsimp only at hfix
  rw [t.first] at hfix
  have hEK : E ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    hfix.2.2.1.symm.le.trans inf_le_right
  have hET : E ≤ Q d.radical t.edge := SmallMover.join_le _ _ _ _
  have hTa : Q d.radical t.edge ≤ stabilizer d.radical r.start :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_start)
  have hEN : E ≤ normalizer (N : Set (FreeAmalgam d.radical)) :=
    (le_inf hEK ((hET.trans hTa).trans (Z_normalized d.radical r.start))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hZV : Z d.radical t.start ≤ V d.radical r.start :=
    neighbor_seed_le_radius t.adjacent_start t.adjacent_shift
  have hNV : N ≤ V d.radical r.start := sup_le (inf_le_left.trans hZV) (Z_le_VBall d.radical r.start 2)
  have hVG : V d.radical r.start ≤ stabilizer d.radical r.start :=
    (replacementGeometry h d).V_local r.start r.path.start_color (by
      rw [(replacementGeometry h d).distance_constant r.start r.path.start_color]
      exact hb2)
  let := finite_stabilizer d.radical r.start
  let : Finite (Z d.radical t.start ⊔ Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (sup_le (hZV.trans hVG) (Z_le_stabilizer d.radical r.start)))
      (inclusion_injective _)
  have hNi : (Z d.radical r.start).relIndex N ≤ 8 :=
    (relIndex_le_of_le_right (show N ≤ Z d.radical t.start ⊔ Z d.radical r.start from
      sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
        (SylowSpanSelection.adjacent_seed_span_index_le_eight
          (e := e) (hz := hz) (hn := hn) hb r.path.start_color t.adjacent_start t.adjacent_shift)
  have hres : ¬ Ltilde d.radical r.start ≤ normalizer (N : Set (FreeAmalgam d.radical)) := by
    intro hnN
    exact hnot (le_sup_left.trans (residual_small_radius_le_slice_knownSimple (e := e)
      hb2 r.path.start_color N hNV hnN hNi))
  refine ⟨hki,hnot,hEN,hres,?_,?_⟩
  · intro hnZ
    have hcore : Q d.radical r.start ≤ E := by
      by_contra hnQ
      have hg := opposite_residual_of_core_not_le_knownSimple
        (e := e) (hz := hz) (hn := hn) hb r.path.start_color
        t.adjacent_start t.adjacent_shift (Z d.radical z) t.generation hnQ
      exact hres (hg.2.trans (sup_le hEN hnZ))
    refine ⟨hcore,?_⟩
    intro hsplit
    by_contra hne
    exact EightUnequalCore.unequal_containing_core_not_centrally_generated_knownSimple
      (e := e) (hz := hz) (hn := hn) hb r.path.start_color
      t.adjacent_start t.adjacent_shift hne hcore hsplit
  · intro hnZ
    let F := Z d.radical z ⊓ Q d.radical r.start
    have htcol : color d.radical t.edge = true := by
      have hh := adjacent_color_ne d.radical t.adjacent_start
      rw [r.path.start_color] at hh
      cases he : color d.radical t.edge <;> simp_all
    have hFT : F ≤ Q d.radical t.edge := inf_le_right.trans
      (Q_le_adjacent_h d.radical htcol t.adjacent_start)
    have hzv : (cosetGraph d.radical).dist z v = 2 := by
      rw [SimpleGraph.dist_comm,r.path.dist_end]
      have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
      omega
    have hFv : F ≤ Q d.radical v := inf_le_left.trans (Z_le_Q_of_dist_lt d.radical z
      ((replacementGeometry h d).exists_critical z r.path.end_color) (by
        rw [(replacementGeometry h d).distance_constant z r.path.end_color,hzv]
        exact hb2))
    have hD : ⁅Z d.radical t.start,Z d.radical v⁆ ≤ Z d.radical v :=
      ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
        (DistanceEight.U_le_Z d.radical v)
    have hFD : F ≤ centralizer ((⁅Z d.radical t.start,Z d.radical v⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) :=
      hFv.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical v t.path.end_color))).trans (centralizer_le hD))
    have hFE : F ≤ E := (le_inf hFT hFD).trans_eq hfix.1
    have hFN : F ≤ normalizer (K : Set (FreeAmalgam d.radical)) := hFE.trans hEK
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
    exact SylowTerminalKernel.restricted_seed_kernel_line_knownSimple (e := e) (hz := hz) (hn := hn)
      hb r.path hrs K (IsElementaryAbelian.of_le inf_le_left) (inf_le_left.trans hZV)
      inf_le_right hFN hnZ

include e hz hn in
private theorem three_shift_kernel_placements
    (hb : 4 < replacementDistance h d)
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
  have hfix := EightTrappedKernel.common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path hsmall ht.2.2.2.2
  dsimp only at hfix
  rw [t.first] at hfix
  have hFJ : F ≤ J := (le_inf hFT hFcent).trans_eq hfix.1
  have hact := EightTrappedKernel.small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path hsmall ht.2.2.2.2
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
  have hDcommon := EightBackwardKernel.common_kernel_line_displacement_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path hsmall ht.2.2.2.2
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
    (SylowTerminalIntersection.edge_seed_central htcol).trans (centralizer_le hFT)
  have hHU : H ≤ U d.radical t.start := by
    apply (commutator_mono inf_le_left le_rfl).trans
    rw [DistanceTwo.CentralLayer.Z_eq_moving_sup_edge_at h e hz d t.path.start_color t.adjacent_shift,
      commutator_sup_fixed _ _ F hseedN hseedF]
    exact le_normalizer_iff_commutator_le_left.mp hFU
  exact ⟨sup_le (hHz.trans (Z_le_VBall d.radical z 2)) hDV,sup_le hHU hDU,sup_le hHW hDW⟩

include e hz hn in
/-- The restricted and critical lines split over their entire central attachment, which is fixed by all three starting stabilizers. -/
theorem three_shift_kernel_central_decomposition_knownSimple
    (hb : 4 < replacementDistance h d)
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
  have hp := three_shift_kernel_placements (e := e) (hz := hz) (hn := hn) hb p q r t
  have hc := SylowTerminalIntersection.three_shift_radius_intersection_central hb p q r t
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
  have hd := EightBackwardKernel.line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path hsmall x hx hxm
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
private theorem three_shift_nonnormalized_central_alternative_knownSimple
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
  have hker := (three_shift_kernel_control_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t).2.2.2.2.2 hnorm
  have hfull := SylowTerminalKernel.three_shift_nonnormalized_full_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hnorm
  have hc := three_shift_kernel_central_decomposition_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t
  have hp := three_shift_kernel_placements (e := e) (hz := hz) (hn := hn) hb p q r t
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
    rw [SylowTerminalIntersection.fixed_map I (stabilizer d.radical r.start) hc.2.1 t.transporter_mem] at hh
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

include e hz hn in
private theorem three_shift_kernel_central_along_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    (∀ i, 2*i ≤ r.path.walk.length → I ≤ centralizer
      (stabilizer d.radical (r.path.walk.getVert (2*i)) : Set (FreeAmalgam d.radical))) ∧
    I ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let I := (H ⊔ D) ⊓ Z d.radical t.edge
  have hc := three_shift_kernel_central_decomposition_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hall := central_along_orbit_path r.path hr I hc.2.1 (by simpa only [hr2] using hc.2.2.1)
  refine ⟨hall,?_⟩
  obtain ⟨n,hn⟩ := replacementDistance_even h d
  have hl : r.path.walk.length = 2*n := r.path.length_eq_b.trans (by change replacementDistance h d = _; omega)
  have hh := hall n (by omega)
  rw [←hl,SimpleGraph.Walk.getVert_length] at hh
  exact hh

include e hz hn in
private theorem three_shift_attachment_along_path_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    H = D ∨ (Nat.card I = 2 ∧
      ∀ i, 4*i+2 ≤ r.path.walk.length → I = U d.radical (r.path.walk.getVert (4*i+2)) ⊓
        centralizer (stabilizer d.radical (r.path.walk.getVert (4*i+2)) :
          Set (FreeAmalgam d.radical))) := by
  have ha := three_shift_nonnormalized_central_alternative_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p q r t hnorm
  rcases ha.2.2 with he | he
  · exact Or.inl he
  · have hc := three_shift_kernel_central_along_path_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr
    have hr2 : r.path.walk.getVert 2 = q.start := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
    exact Or.inr ⟨he.2.2,attachment_along_orbit_path r.path hr _ hc.1 (by
      simpa only [hr2] using he.2.1)⟩

include e hz hn in
private theorem three_shift_nonnormalized_lines_knownSimple
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
    let K := Z d.radical t.start ⊓ Q d.radical v
    (¬ ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ ≤
      centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))) ∧
    (¬ ⁅Z d.radical r.start,Z d.radical z⁆ ≤ Z d.radical t.start) := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  have hr := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hrs : (Q d.radical z).relIndex (Z d.radical r.start) < 4 := by rw [hr.2.1]; decide
  have hk := (three_shift_kernel_control_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p q r t).2.2.2.2.2 hnorm
  have hne : ⁅Z d.radical z ⊓ Q d.radical r.start,K⁆ ≠ ⊥ := by
    intro he
    rw [commutator_comm] at he
    have hh : Nat.card (⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 := hk.1
    rw [he,Subgroup.card_bot] at hh
    omega
  have hKQ : K ≤ Q d.radical r.start :=
    (inf_le_left.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q hb2 r.start r.path.start_color)
  have hn := critical_predecessor_kernel_noncentral s hc hb2 r.path hrs K hKQ inf_le_right hne
  rw [commutator_comm] at hn
  exact ⟨hn,backwardShift_critical_line_not_le_seed s hc hb2 r.path t⟩

include e hz hn in
/-- Failure of terminal normalization makes the full endpoint moving central attachment escape the last seed. -/
theorem three_shift_nonnormalized_attachment_escape_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    ¬ U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t.start := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let F := Z d.radical z ⊓ Q d.radical r.start
  let H := ⁅K,F⁆
  let D := ⁅Z d.radical r.start,Z d.radical z⁆
  let C := Z d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  change ¬ U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤ Z d.radical t.start
  intro hattach
  have hk := (three_shift_kernel_control_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p q r t).2.2.2.2.2 hnorm
  have hlines := three_shift_nonnormalized_lines_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hnorm
  have hr := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hcardD : Nat.card D = 2 := hr.2.2.2.1
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hKG : K ≤ stabilizer d.radical z := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical v z t.path.end_color hvz)
  have hHU : H ≤ U d.radical z := by
    dsimp only [H,F]
    rw [(critical_kernel_predecessor_moving s hc hb2 r.path).2.2 K inf_le_right
      |> fun hh => (by simpa only [commutator_comm K] using hh :
        ⁅K,Z d.radical z ⊓ Q d.radical r.start⁆ = ⁅K,U d.radical z ⊓ Q d.radical r.start⁆)]
    exact (commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hKG.trans (U_normalized z)))
  have hDU : D ≤ U d.radical z :=
    (critical_Z_commutator_le_moving (h := h) r.path).trans inf_le_right
  have hDG : D ≤ stabilizer d.radical z :=
    (hDU.trans (DistanceEight.U_le_Z d.radical z)).trans (Z_le_stabilizer d.radical z)
  have hCN : C ≤ normalizer (D : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans (centralizer_le hDG)).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hlines.1
  have hxprod : x ∈ (D : Set (FreeAmalgam d.radical)) * (C : Set (FreeAmalgam d.radical)) := by
    rw [←coe_mul_of_right_le_normalizer_left D C hCN]
    exact hk.2.2 hx
  obtain ⟨a,ha,c,hcC,hac⟩ := hxprod
  have hcU : c ∈ U d.radical z := by
    have he : c = a⁻¹*x := by rw [←hac]; simp
    rw [he]
    exact (U d.radical z).mul_mem ((U d.radical z).inv_mem (hDU ha)) (hHU hx)
  have hcT : c ∈ Z d.radical t.start := by
    exact hattach ⟨hcU,hcC.2⟩
  have haT : a ∈ Z d.radical t.start := by
    have he : a = x*c⁻¹ := by rw [←hac]; simp
    rw [he]
    exact (Z d.radical t.start).mul_mem (hk.2.1 hx).1 ((Z d.radical t.start).inv_mem hcT)
  have hane : a ≠ 1 := by
    intro ha1
    apply hxc
    rw [←hac,ha1]
    simp
    exact hcC.2
  let := finite_Z d.radical z
  let : Finite D := Finite.of_injective
    (inclusion (hDU.trans (DistanceEight.U_le_Z d.radical z))) (inclusion_injective _)
  let : Finite (D ⊓ Z d.radical t.start : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hne : D ⊓ Z d.radical t.start ≠ ⊥ := by
    intro he
    have hh : a ∈ D ⊓ Z d.radical t.start := ⟨ha,haT⟩
    rw [he,mem_bot] at hh
    exact hane hh
  have hlo := (one_lt_card_iff_ne_bot (D ⊓ Z d.radical t.start)).mpr hne
  have heq : D ⊓ Z d.radical t.start = D := eq_of_le_of_card_ge inf_le_left (by omega)
  have hDle : D ≤ Z d.radical t.start := by
    rw [← heq]
    exact inf_le_right
  exact hlines.2 hDle

include e hz hn in
/-- At distance six, orbit propagation forces coincident restricted and critical lines in any nonnormalizing branch. -/
theorem six_nonnormalized_coincident_lines_knownSimple
    (hb : replacementDistance h d = 6)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆ =
      ⁅Z d.radical t.start,Z d.radical v⁆ ∧
    ¬ U d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t.start := by
  have hb4 : 4 < replacementDistance h d := by omega
  have he := three_shift_nonnormalized_attachment_escape_knownSimple (e := e) (hz := hz) (hn := hn) hb4 p q r t hnorm
  refine ⟨?_,he⟩
  rcases three_shift_attachment_along_path_knownSimple (e := e) (hz := hz) (hn := hn)
    hb4 p q r t hr hnorm with hh | hh
  · exact hh
  · have hl : r.path.walk.length = 6 := r.path.length_eq_b.trans hb
    have hi := hh.2 1 (by omega)
    have hc := three_shift_kernel_central_decomposition_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 p q r t
    have hend : r.path.walk.getVert (4*1+2) = q.path.walk.getVert (q.path.walk.length-2) := by
      rw [show 4*1+2 = r.path.walk.length by omega,r.path.walk.getVert_length]
    rw [hend] at hi
    exact (he (hi ▸ hc.1.trans (DistanceEight.U_le_Z d.radical t.start))).elim

end EightTerminal
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
