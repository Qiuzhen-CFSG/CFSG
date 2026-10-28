module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCoreSaturation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTrappedMover
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair

/-!
# Whole-core normalization and the image-sixteen terminal contradiction

Two conjugate index-two critical kernels generate the full starting seed.
The common kernel is the critical line times the full edge-fixed seed.
Since the edge normalizes the entire neighboring core, conjugating its
restricted movement through this product recovers the whole core
commutator as the join of the critical line and the restricted movement.

The full endpoint omega group centralizes the line and normalizes the
restricted movement. Together with the generating edge this makes the
whole core commutator invariant under the intermediate stabilizer. Its
proved order bound of eight then forces the original A6 residual to fix it,
contradicting the escaping critical line. This excludes every distance
greater than four when the actual replacement radical has image sixteen,
including distance six and both moving-cover orders sixteen and thirty-two.

The proof uses the natural replacement graph, its actual whole cores and
the original radical transporter throughout. The elementary conjugation
argument is adapted from the independent exceptional branch's
OriginalSylow/WholeCoreMovement; no graph or radical identification is used.
The remaining branch above four has non-elementary image eight and index
two in the original radical. Its exclusion and the distance-four estimates
remain necessary for the unconditional distance-two conclusion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.9)--(5.11), printed pp.921--924. The small-order A6 action
argument specializes the terminal step to the actual binary covers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowWholeCore
private theorem conjugate_kernel_movement {F : Type*} [Group F]
    (V K A B D C : Subgroup F) [IsMulCommutative V]
    (x : F) (hK : K ≤ V) (hBA : B ≤ A)
    (hAV : A ≤ normalizer (V : Set F))
    (hxV : x ∈ normalizer (V : Set F))
    (hxA : x ∈ normalizer (A : Set F))
    (hgen : K ⊔ K.map (MulAut.conj x).toMonoidHom = V)
    (hKB : K ≤ centralizer (B : Set F))
    (hD : D = ⁅V,B⁆) (hDC : D ⊔ C ≤ V)
    (hCx : x ∈ centralizer (C : Set F))
    (hbound : ⁅V,A⁆ ≤ D ⊔ C) :
    ⁅V,A⁆ = D ⊔ ⁅K,A⁆ := by
  let f := (MulAut.conj x).toMonoidHom
  let K' := K.map f
  let B' := B.map f
  let E := ⁅K,A⁆
  let N := D ⊔ E
  have hV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp hxV
  have hA : A.map f = A := mem_normalizer_iff_map_conj_eq.mp hxA
  have hEV : E ≤ V := (commutator_mono hK le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hAV)
  have hNV : N ≤ V := sup_le (le_sup_left.trans hDC) hEV
  have hVN : V ≤ normalizer (N : Set F) :=
    ((le_centralizer V).trans (centralizer_le hNV)).trans (Subgroup.centralizer_le_normalizer _)
  have hVE : V ≤ normalizer (E : Set F) :=
    ((le_centralizer V).trans (centralizer_le hEV)).trans (Subgroup.centralizer_le_normalizer _)
  have hK' : K' ≤ V := (map_mono hK).trans_eq hV
  have hB' : B' ≤ A := (map_mono hBA).trans_eq hA
  have hzero : ⁅K',B'⁆ = ⊥ := by
    rw [show K' = K.map f from rfl,show B' = B.map f from rfl,←map_commutator,
      commutator_eq_bot_iff_le_centralizer.mpr hKB,Subgroup.map_bot]
  have hD' : D.map f ≤ E := by
    rw [hD,map_commutator,hV]
    rw [←hgen]
    exact commutator_sup_le_of_relative_normal V K K' B' E hVE hK hK'
      (commutator_mono le_rfl hB') (hzero.le.trans bot_le)
  have hCN : C ≤ normalizer (D : Set F) :=
    (((show C ≤ V from le_sup_right.trans hDC).trans ((le_centralizer V).trans
      (centralizer_le (show D ≤ V from le_sup_left.trans hDC)))).trans
        (Subgroup.centralizer_le_normalizer _))
  have hEmap : E.map f ≤ N := by
    rintro _ ⟨y,hy,rfl⟩
    have hyDC : y ∈ (D : Set F) * (C : Set F) := by
      rw [←coe_mul_of_right_le_normalizer_left D C hCN]
      exact hbound (commutator_mono hK le_rfl hy)
    obtain ⟨d,hd,c,hc,he⟩ := hyDC
    have hfc : f c = c := by
      change x*c*x⁻¹=c
      rw [←hCx c hc,mul_inv_cancel_right]
    have hfe : f y = f d * d⁻¹ * y := by
      rw [←he,map_mul,hfc]
      group
    rw [hfe]
    exact N.mul_mem (N.mul_mem (mem_sup_right (hD' (mem_map_of_mem f hd)))
      (mem_sup_left (D.inv_mem hd))) (mem_sup_right hy)
  apply le_antisymm
  · rw [←hgen]
    apply commutator_sup_le_of_relative_normal V K K' A N hVN hK hK'
      le_sup_right
    have hm : ⁅K',A⁆ = E.map f := by rw [show E = ⁅K,A⁆ from rfl,map_commutator,hA]
    exact hm.trans_le hEmap
  · exact sup_le (hD ▸ commutator_mono le_rfl hBA) (commutator_mono hK le_rfl)


universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem small_mover_whole_seed_bound
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
  have hdec := SylowKernelDecomposition.sixteen_line_mover_common_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hs x hx hxm
  have hk := SylowTrappedMover.sixteen_small_mover_full_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p hs hm
  have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  have hT := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) hcard p.start_color hat
  have hp := SylowKernelPair.small_kernel_pair_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hs x (hT.symm ▸ hx) hxm
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
/-- The whole neighboring-core movement is the join of the terminal critical
line and the movement of the full restricted kernel. -/
theorem orbit_terminal_whole_core_decomposition_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
    (e := e) (hz := hz) (hn := hn) hb hcard p q r t hr
  have hj := SylowAdjacent.sixteen_edge_small_mover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard t.path.start_color t.adjacent_shift
  have hAV := (hAJ.trans hj.2.1).trans hTV
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
      hb hcard t.path hs (by simpa only [t.first] using hm)
    dsimp only at hh
    rw [t.first] at hh
    exact (commutator_mono le_rfl hAJ).trans hh
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) t.start t.path.start_color
  exact conjugate_kernel_movement V K A (Z d.radical v) D C x inf_le_left hvA hAV
    (hTV hx) (hTA hx) hgen hKB rfl hDC
    (le_centralizer_iff.mp (show C ≤ centralizer (T : Set _) from inf_le_right) hx) hbound

include e hz hn in
private theorem restricted_movement_omega_normalized
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
    (e := e) (hz := hz) (hn := hn) hb hcard p q r t hr
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
/-- The full endpoint omega group normalizes the entire neighboring-core
commutator on the actual natural replacement graph, including distance six. -/
theorem orbit_terminal_whole_core_omega_normalized_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
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
    (e := e) (hz := hz) (hn := hn) hb hcard p q r t hr]
  exact (le_inf ((le_centralizer_iff.mp hDX).trans (Subgroup.centralizer_le_normalizer _))
    (restricted_movement_omega_normalized (e := e) (hz := hz) (hn := hn)
      hb hcard p q r t hr)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

include e hz hn in
/-- Whole-core invariance contradicts the escaping critical line: the
original A6 residual fixes every invariant core subgroup of order at most eight. -/
theorem orbit_terminal_false_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : SylowTerminalPath.OrbitPrefix (h := h) r.path (replacementDistance h d)) : False := by
  let W := ⁅Z d.radical t.start,Q d.radical r.start⁆
  have hnot := (orbit_terminal_core_commutator_not_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p q r t hr).2.2.1
  apply hnot
  apply (Ltilde_le_stabilizer r.start).trans
  have hZX : Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤
      X d.radical (q.path.walk.getVert (q.path.walk.length-2)) := by
    apply (replacementGeometry h d).omega_bound _ r.path.end_color
    rw [(replacementGeometry h d).distance_constant _ r.path.end_color]
    exact replacementDistance_pos h d
  rw [←t.generation]
  apply sup_le _ (hZX.trans (orbit_terminal_whole_core_omega_normalized_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p q r t hr))
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
/-- The original radical's actual transporter and orbit chain give the
terminal contradiction. No Sylow assumption on the original radical is used. -/
theorem original_radical_terminal_false_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) : False := by
  obtain ⟨q₀,_,_,_,c,c',p₀,_,q,r,t,hr,_⟩ :=
    original_radical_orbit_terminal_normalization_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hfirst
  exact orbit_terminal_false_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hcard p₀ q r t hr

include e hz hn in
/-- Radical image sixteen forces critical distance at most four on the actual
minimum characteristic replacement, with either moving-cover order. -/
theorem sixteen_image_distance_le_four_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    replacementDistance h d ≤ 4 := by
  by_contra! hb
  obtain ⟨z,⟨p⟩⟩ := CriticalPath.exists_from (R := d.radical)
    (geometry := replacementGeometry h d) (a := alpha d.radical) rfl
  obtain ⟨c,c',p₀,_,hp₀⟩ := SylowTerminalPath.exists_orbitPrefix_chain_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hcard p (replacementDistance h d)
  obtain ⟨q,_⟩ := SylowShiftChain.backwardShift_with_edge
    (e := e) (hz := hz) (hn := hn) hb hcard p₀
  obtain ⟨r,_⟩ := SylowShiftChain.backwardShift_with_edge
    (e := e) (hz := hz) (hn := hn) hb hcard q.path
  obtain ⟨t,_⟩ := SylowShiftChain.backwardShift_with_edge
    (e := e) (hz := hz) (hn := hn) hb hcard r.path
  have hq := SylowTerminalPath.orbitPrefix_backwardShift hb p₀ q hp₀
  have hr := SylowTerminalPath.orbitPrefix_backwardShift hb q.path r hq
  exact orbit_terminal_false_knownSimple (e := e) (hz := hz) (hn := hn)
    hb hcard p₀ q r t (fun i hi hl => hr i (by omega) hl)

include e hz hn in
/-- Positivity and parity leave precisely two or four in the image-sixteen
branch of the actual characteristic replacement. -/
theorem sixteen_image_distance_two_or_four_knownSimple
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16) :
    replacementDistance h d = 2 ∨ replacementDistance h d = 4 := by
  have hle := sixteen_image_distance_le_four_knownSimple
    (e := e) (hz := hz) (hn := hn) hcard
  have hp := replacementDistance_pos h d
  have he := replacementDistance_even h d
  rw [Nat.even_iff] at he
  omega

include e hz hn in
/-- The surviving branch above four has non-elementary image eight and
index two in the original radical. This applies the terminal exclusion
through the literal original-radical reduction and quotient map. -/
theorem four_lt_original_sylow_eight_image_knownSimple
    (hb : 4 < replacementDistance h d) :
    (∃ P : Sylow 2 (L ⊔ R : Subgroup G),
      (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) ∧
      (¬ IsElementaryAbelian 2
        (d.radical.map (SourceReduction.projection h e hz hn d))) ∧
      d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 2 ∧
      Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8 := by
  obtain ⟨hSyl,hne,hcases⟩ :=
    SylowTerminal.four_lt_original_sylow_non_elementary_image_knownSimple
      (e := e) (hz := hz) (hn := hn) hb
  rcases hcases with ⟨_,h16⟩ | h8
  · exact False.elim ((Nat.not_le_of_gt hb)
      (sixteen_image_distance_le_four_knownSimple (e := e) (hz := hz) (hn := hn) h16))
  · exact ⟨hSyl,hne,h8⟩


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
