module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.EightTerminalNormalization
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowWholeCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowWholeCore
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair

/-!
# The whole-core contradiction and the complete distance-four bound

Two conjugate critical kernels generate the entire terminal seed. Their
common kernel is the critical line times the full edge-fixed seed. The
actual edge normalizes the neighboring whole core, so conjugation recovers
its entire commutator from the critical line and the restricted movement.

The full endpoint omega group normalizes this whole commutator. Together
with the generating edge it makes the commutator invariant under the
intermediate stabilizer. Its order is at most eight on both moved covers;
the original perfect A6 component must therefore fix it. This contradicts
the noncentral critical line inside it.

EightGenerating and EightChain construct every shift and orbit relation
used here. Their image-eight reduction preserves index two in the restricted
original radical; the actual edge core is never identified with that radical
or with its relative normalizer. The already proved image-sixteen exclusion
and the remaining image-eight contradiction now give distance at most four
for every original minimum characteristic replacement. Distance four is the
separate source-(5.12) obligation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10)--(5.11), printed pp.922--924. The conjugate-kernel identity
and the small A6 action lemma are reused from SylowWholeCore and
SylowCoreSaturation on the same natural graph.
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
private theorem orbit_terminal_line_in_omega_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let z := r.path.walk.getVert (r.path.walk.length-2)
    let D := ⁅Z d.radical t.start,Z d.radical z⁆
    Nat.card D = 2 ∧ D ≤ X d.radical r.start ∧
      ¬ D ≤ centralizer (stabilizer d.radical r.start : Set (FreeAmalgam d.radical)) := by
  let z := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z d.radical t.start,Z d.radical z⁆
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hsmall : (Q d.radical z).relIndex (Z d.radical t.start) < 4 := by rw [ht.2.1]; decide
  have hfix := EightTrappedKernel.common_kernel_centralizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path hsmall ht.2.2.2.2
  dsimp only at hfix
  rw [t.first] at hfix
  have hcore := orbit_terminal_core_containment_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr
  have hDC : D ≤ centralizer (Q d.radical r.start : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp ((hcore.trans hfix.1.symm.le).trans inf_le_right)
  have hDZ : D ≤ Z d.radical t.start :=
    ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical t.start)
  have hDQ : D ≤ Q d.radical r.start :=
    (hDZ.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q (by omega : 2 < replacementDistance h d) r.start r.path.start_color)
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
  refine ⟨ht.2.2.2.1,?_,ht.1⟩
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hDQ hx,elemPow_eq_one_of_isElementaryAbelian x (hDZ hx),hDC hx⟩

include e hz hn in
private theorem orbit_terminal_line_not_le_fixedCore_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    ¬ ⁅Z d.radical t.start,Z d.radical (r.path.walk.getVert (r.path.walk.length-2))⁆ ≤
      fixedCore d.radical r.start := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hs := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r
  have hsmall : (Q d.radical (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z d.radical r.start) < 4 := by rw [hs.2.1]; decide
  have hcentral := omega_fixed_central_of_small_critical s hc r.path hsmall r.start r.path.start_color
  have hline := orbit_terminal_line_in_omega_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr
  intro hfixed
  exact hline.2.2 ((le_inf hline.2.1 hfixed).trans hcentral)

include e hz hn in
private theorem orbit_terminal_core_commutator_not_normalized_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let W := ⁅Z d.radical t.start,Q d.radical r.start⁆
    W ≤ Q d.radical r.start ∧ Nat.card W ≤ 8 ∧
      (¬ Ltilde d.radical r.start ≤ normalizer (W : Set (FreeAmalgam d.radical))) ∧
      ¬ W ≤ centralizer (Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) :
        Set (FreeAmalgam d.radical)) := by
  let W := ⁅Z d.radical t.start,Q d.radical r.start⁆
  let z := r.path.walk.getVert (r.path.walk.length-2)
  have hcore := orbit_terminal_core_containment_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr
  have hsmall := EightTrappedKernel.small_mover_seed_commutator_card_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path.start_color t.adjacent_shift
    (Q d.radical r.start) hcore
  have hZQ : Z d.radical t.start ≤ Q d.radical r.start :=
    (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift).trans
      ((replacementGeometry h d).V_le_Q (by omega : 2 < replacementDistance h d)
        r.start r.path.start_color)
  have hWQ : W ≤ Q d.radical r.start :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le hZQ le_rfl)
  have hzQ : Z d.radical z ≤ Q d.radical r.start := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z t.path.end_color)
    rw [(replacementGeometry h d).distance_constant z t.path.end_color,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist r.start (r.path.walk.getVert (r.path.walk.length-2)) < _
    rw [r.path.dist_start (Nat.sub_le _ _)]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    change r.path.walk.length-2 < replacementDistance h d
    omega
  have hnot : ¬ Ltilde d.radical r.start ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    intro hnorm
    have hfixed := small_core_residual_fixed_knownSimple (h := h) (e := e)
      r.path.start_color W hWQ hnorm hsmall
    exact orbit_terminal_line_not_le_fixedCore_knownSimple (e := e) (hz := hz) (hn := hn) hb p q r t hr
      ((commutator_mono le_rfl hzQ).trans hfixed)
  refine ⟨hWQ,hsmall,hnot,?_⟩
  intro hcentral
  apply hnot
  apply (Ltilde_le_stabilizer r.start).trans
  rw [←t.generation]
  apply sup_le _ ((le_centralizer_iff.mp hcentral).trans (Subgroup.centralizer_le_normalizer _))
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change W.map (MulAut.conj x).toMonoidHom = W
  dsimp only [W]
  have hzmap : (Z d.radical t.start).map (MulAut.conj x).toMonoidHom = Z d.radical t.start :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical t.start
      (hx.2 _ (adjacent_symm d.radical t.adjacent_shift)))
  have hqmap : (Q d.radical r.start).map (MulAut.conj x).toMonoidHom = Q d.radical r.start :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical r.start
      (hx.2 _ (adjacent_symm d.radical t.adjacent_start)))
  rw [map_commutator,hzmap,hqmap]

include e hz hn in
private theorem small_mover_whole_seed_bound
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hs : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (hm : ¬ Q d.radical (p.walk.getVert 1) ≤ centralizer
      ((⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := Q d.radical (p.walk.getVert 1)
    let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
    ⁅Z d.radical a,J⁆ ≤ ⁅Z d.radical a,Z d.radical z⁆ ⊔
      (Z d.radical a ⊓ centralizer (T : Set (FreeAmalgam d.radical))) := by
  let T := Q d.radical (p.walk.getVert 1)
  let K := Z d.radical a ⊓ Q d.radical z
  let F := Z d.radical a ⊓ centralizer (componentOrbit (Z d.radical z) T : Set _)
  let J := SmallMover.join (U d.radical a) (Q d.radical a) T 4
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp hm
  have hdec := EightBackwardKernel.line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hs x hx hxm
  have hk := EightTrappedKernel.small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hs hm
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hp := SylowKernelPair.small_kernel_pair_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hs x ⟨T.le_normalizer hx,hx.2 a (adjacent_symm d.radical hat)⟩ hxm
  have hgen : K ⊔ K.map (MulAut.conj x).toMonoidHom = Z d.radical a := hp.2.2.1
  have hZmap : (Z d.radical a).map (MulAut.conj x).toMonoidHom = Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized d.radical a (hx.2 a (adjacent_symm d.radical hat)))
  have hxZ : K.map (MulAut.conj x).toMonoidHom ≤ Z d.radical a :=
    (map_mono inf_le_left).trans_eq hZmap
  have h1 : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom =
      MonoidHom.id (FreeAmalgam d.radical) := by
    apply MonoidHom.ext
    intro y
    simp
  have hKJ : ⁅K,J⁆ ≤ F := by
    simpa only [h1,Subgroup.map_id] using (hk 1 T.one_mem).2.2.1
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  have hZF : Z d.radical a ≤ normalizer (F : Set (FreeAmalgam d.radical)) :=
    ((le_centralizer (Z d.radical a)).trans (centralizer_le inf_le_left)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hbound : ⁅Z d.radical a,J⁆ ≤ F := by
    rw [←hgen]
    exact commutator_sup_le_of_relative_normal (Z d.radical a) K
      (K.map (MulAut.conj x).toMonoidHom) J F hZF inf_le_left hxZ hKJ (hk x hx).2.2.1
  exact hbound.trans_eq hdec.1

include e hz hn in
/-- The entire neighboring-core commutator is the critical line joined with the movement of the full restricted kernel. -/
theorem orbit_terminal_whole_core_decomposition_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z d.radical t.start,Q d.radical r.start⁆ =
      ⁅Z d.radical t.start,Z d.radical v⁆ ⊔
      ⁅Z d.radical t.start ⊓ Q d.radical v,Q d.radical r.start⁆ := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let V := Z d.radical t.start
  let K := V ⊓ Q d.radical v
  let A := Q d.radical r.start
  let T := Q d.radical t.edge
  let J := SmallMover.join (U d.radical t.start) (Q d.radical t.start) T 4
  let D := ⁅V,Z d.radical v⁆
  let C := V ⊓ centralizer (T : Set (FreeAmalgam d.radical))
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have ht := SylowShiftChain.two_backward_shifts_small_moving_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path r t
  have hs : (Q d.radical v).relIndex V < 4 := by rw [ht.2.1]; decide
  have hm : ¬ T ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    simpa only [t.first] using ht.2.2.2.2
  have hTG : T ≤ stabilizer d.radical t.start := fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_shift)
  have hTr : T ≤ stabilizer d.radical r.start := fun _ hx => hx.2 _ (adjacent_symm d.radical t.adjacent_start)
  have hTV : T ≤ normalizer (V : Set (FreeAmalgam d.radical)) := hTG.trans (Z_normalized d.radical t.start)
  have hTA : T ≤ normalizer (A : Set (FreeAmalgam d.radical)) := hTr.trans (Q_normalized d.radical r.start)
  have hAJ : A ≤ J := orbit_terminal_core_containment_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hr
  have hj := EightSmallMovers.edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb t.path.start_color t.adjacent_shift
  have hAV := (hAJ.trans hj.2.2.2.1).trans hTV
  have hvA : Z d.radical v ≤ A := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v t.path.end_color)
    rw [SimpleGraph.dist_comm,r.path.dist_start (Nat.sub_le _ _),
      (replacementGeometry h d).distance_constant _ t.path.end_color]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    change r.path.walk.length-2 < replacementDistance h d
    omega
  obtain ⟨x,hx,hxm⟩ := SetLike.not_le_iff_exists.mp hm
  have hxn : x ∉ normalizer (K : Set (FreeAmalgam d.radical)) := by
    intro hnx
    have hh : x ∈ stabilizer d.radical t.start ⊓ normalizer (K : Set (FreeAmalgam d.radical)) := ⟨hTG hx,hnx⟩
    rw [small_critical_kernel_normalizer_eq_line_centralizer s hc t.path hs] at hh
    exact hxm hh.2
  let f := (MulAut.conj x).toMonoidHom
  have hV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp (hTV hx)
  have hKi : K.relIndex V = 2 := by
    rw [show K = V ⊓ Q d.radical v from rfl,inf_relIndex_left]
    exact ht.2.1
  let := finite_Z d.radical t.start
  have hgen : K ⊔ K.map f = V :=
    (SylowKernelPair.two_hyperplanes V K (K.map f) inf_le_left
      ((map_mono (show K ≤ V from inf_le_left)).trans_eq hV) hKi
      (by rw [←hV,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]; exact hKi)
      (fun he => hxn (mem_normalizer_iff_map_conj_eq.mpr he.symm))).1
  have hKB : K ≤ centralizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical v t.path.end_color)))
  have hDC : D ⊔ C ≤ V := sup_le
    (((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical t.start)) inf_le_left
  have hbound : ⁅V,A⁆ ≤ D ⊔ C := by
    have hh := small_mover_whole_seed_bound (e := e) (hz := hz) (hn := hn)
      hb t.path hs (by simpa only [t.first] using hm)
    dsimp only at hh
    rw [t.first] at hh
    exact (commutator_mono le_rfl hAJ).trans hh
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
  exact SylowWholeCore.conjugate_kernel_movement V K A (Z d.radical v) D C x inf_le_left hvA hAV
    (hTV hx) (hTA hx) hgen hKB rfl hDC
    (le_centralizer_iff.mp (show C ≤ centralizer (T : Set _) from inf_le_right) hx) hbound

include e hz hn in
private theorem restricted_movement_omega_normalized
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    X d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      ((⁅Z d.radical t.start ⊓ Q d.radical v,Q d.radical r.start⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z d.radical t.start ⊓ Q d.radical v
  let N := K ⊔ Z d.radical r.start
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hKQ : K ≤ Q d.radical r.start :=
    (inf_le_left.trans (neighbor_seed_le_radius t.adjacent_start t.adjacent_shift)).trans
      ((replacementGeometry h d).V_le_Q hb2 r.start r.path.start_color)
  have hcomm : ⁅N,Q d.radical r.start⁆ = ⁅K,Q d.radical r.start⁆ := by
    rw [commutator_comm N,commutator_comm K]
    symm
    exact commutator_eq_of_centralizing_sup (sup_comm _ _)
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical r.start r.path.start_color))
      (hKQ.trans (Q d.radical r.start).le_normalizer)
  have hNX := orbit_terminal_full_omega_normalization_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hr
  have hXG : X d.radical z ≤ stabilizer d.radical r.start :=
    CriticalCriterion.critical_X_le_stabilizer d.radical (replacementGeometry h d)
      (edgeCentralizerCondition s hc) (replacementDistance_pos h d) z r.path.end_color
      r.start (critical_reverse_pair s hc r.path)
  change X d.radical z ≤ normalizer ((⁅K,Q d.radical r.start⁆ : Subgroup _) : Set _)
  rw [←hcomm]
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hNX hx),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical r.start (hXG hx))]

include e hz hn in
/-- The full endpoint omega subgroup normalizes the entire neighboring-core commutator. -/
theorem orbit_terminal_whole_core_omega_normalized_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    X d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      ((⁅Z d.radical t.start,Q d.radical r.start⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  have hDv : D ≤ Z d.radical v :=
    ((critical_Z_commutator_le_moving (h := h) t.path).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical v)
  have hvz : (cosetGraph d.radical).dist v z = 2 := by
    rw [show v = r.path.walk.getVert (r.path.walk.length-2) from rfl,r.path.dist_end]
    have hl : r.path.walk.length = replacementDistance h d := r.path.length_eq_b
    omega
  have hvQ : Z d.radical v ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v t.path.end_color)
    rw [hvz,(replacementGeometry h d).distance_constant _ t.path.end_color]
    change 2 < replacementDistance h d
    omega
  have hDX : D ≤ centralizer (X d.radical z : Set (FreeAmalgam d.radical)) :=
    (hDv.trans hvQ).trans (Q_le_centralizer_X d.radical z)
  rw [orbit_terminal_whole_core_decomposition_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hr]
  exact (le_inf ((le_centralizer_iff.mp hDX).trans (Subgroup.centralizer_le_normalizer _))
    (restricted_movement_omega_normalized (e := e) (hz := hz) (hn := hn)
      hb p q r t hr)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

include e hz hn in
/-- Whole-core invariance contradicts the escaping critical line on the constructed orbit path. -/
theorem orbit_terminal_false_knownSimple
    (hb : 4 < replacementDistance h d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) : False := by
  let W := ⁅Z d.radical t.start,Q d.radical r.start⁆
  have hnot := (orbit_terminal_core_commutator_not_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hr).2.2.1
  apply hnot
  apply (Ltilde_le_stabilizer r.start).trans
  have hZX : Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
      X d.radical (q.path.walk.getVert (q.path.walk.length-2)) := by
    apply (replacementGeometry h d).omega_bound _ r.path.end_color
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color]
    exact replacementDistance_pos h d
  rw [←t.generation]
  apply sup_le _ (hZX.trans (orbit_terminal_whole_core_omega_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p q r t hr))
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change W.map (MulAut.conj x).toMonoidHom = W
  dsimp only [W]
  have hzmap : (Z d.radical t.start).map (MulAut.conj x).toMonoidHom = Z d.radical t.start :=
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical t.start
      (hx.2 _ (adjacent_symm d.radical t.adjacent_shift)))
  have hqmap : (Q d.radical r.start).map (MulAut.conj x).toMonoidHom = Q d.radical r.start :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical r.start
      (hx.2 _ (adjacent_symm d.radical t.adjacent_start)))
  rw [map_commutator,hzmap,hqmap]

include e hz hn in
/-- Every actual minimum characteristic natural replacement has distance at most four, retaining all radical images and both covers. -/
theorem distance_le_four_knownSimple :
    replacementDistance h d ≤ 4 := by
  by_contra! hb
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  obtain ⟨c,c',p₀,_,hp₀⟩ := EightChain.exists_orbitPrefix_chain_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p (replacementDistance h d)
  obtain ⟨q,_⟩ := EightGenerating.backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p₀
  obtain ⟨r,_⟩ := EightGenerating.backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q.path
  obtain ⟨t,_⟩ := EightGenerating.backwardShift_with_edge_knownSimple
    (e := e) (hz := hz) (hn := hn) hb r.path
  have hq := SylowTerminalPath.orbitPrefix_backwardShift hb p₀ q hp₀
  have hr := SylowTerminalPath.orbitPrefix_backwardShift hb q.path r hq
  exact orbit_terminal_false_knownSimple (e := e) (hz := hz) (hn := hn)
    hb p₀ q r t (fun i hi hl => hr i (by omega) hl)


include e hz hn in
/-- Positivity and evenness leave only two or four for the original
minimum characteristic replacement, without a radical-image premise. -/
theorem distance_two_or_four_knownSimple :
    replacementDistance h d = 2 ∨ replacementDistance h d = 4 := by
  have hle := distance_le_four_knownSimple (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  have hpos := replacementDistance_pos h d
  have heven := replacementDistance_even h d
  rw [Nat.even_iff] at heven
  omega

/-- The complete source-(5.11) input on the actual natural replacement.
The source-(3.8) action and central layer are supplied by their proved producers. -/
theorem beyondFour_knownSimple : BeyondFourInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d _ _ hb
  exact (Nat.not_le_of_gt hb)
    (distance_le_four_knownSimple (h := h) (e := e) (hz := hz) (hn := hn) (d := d))

end EightTerminal
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
