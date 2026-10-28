module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusKernel

/-!
# Conjugate-kernel control and the nonsylow distance bound

On either full central cover, equal small critical commutators determine
identical seed kernels. The marked natural quotient gives equality of the
actor images; the whole two-core then fixes the full kernel, including every
central attachment.

At radius index two, any escaping seed fills the same radius image. The
selected seed and its cubic conjugate therefore have equal commutators if
both escape. Quadratic edge action puts this line in both conjugate edge
seeds. Their actual kernels generate the intermediate stabilizer, so that
whole stabilizer centralizes the line. Equality of critical kernels then
places the selected kernel in the conjugate intermediate core. If the
conjugate seed is trapped, this containment follows directly. Both cases
use the same cubic and the literal inverse-conjugation graph convention.

Apply this to the index-four tower from CubeRadiusKernel. The full kernel
and its cubic conjugate have commutators with the two selected endpoint
seeds in the full central seed. The kernel together with that central seed
is consequently normalized by the actual generating edge and both endpoint
seeds, hence lies in the Baumann slice. Its index is at most two, contradicting
the strict slice bound at the same transported vertex. This excludes index
four on the selected path, and the existing four-shift selection gives
replacementDistance <= 4 for every original nonsylow radical.

The proof preserves both moved covers of orders sixteen and thirty-two,
the original minimum characteristic replacement and all central attachments.
It makes no identification with the exceptional cubic graph. The original
Sylow branch and the distance-four residual estimates remain necessary for
largeDistance_knownSimple and unconditional replacementDistance = 2.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.6)(b,c), (5.9), and (5.11)(1), printed pp.917--924, especially
the two conjugate-seed cases on p.923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

private theorem index_two_sup_kernel {F : Type*} [Group F]
    (V Q A : Subgroup F) [Finite V] (hA : A ≤ V)
    (hi : Q.relIndex V=2) (hne : ¬ A ≤ Q) :
    (V ⊓ Q) ⊔ A = V := by
  let K := V ⊓ Q
  let E := K ⊔ A
  have hEV : E ≤ V := sup_le inf_le_left hA
  let : Finite E := Finite.of_injective (inclusion hEV) (inclusion_injective _)
  have hKV : K.relIndex V=2 := by simpa only [K,inf_relIndex_left] using hi
  have hne' : K.relIndex E ≠ 1 := by
    intro hh
    exact hne ((le_sup_right.trans (relIndex_eq_one.mp hh)).trans inf_le_right)
  have hpos : 0 < K.relIndex E := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hp : 0 < E.relIndex V := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have ht := relIndex_mul_relIndex K E V le_sup_left hEV
  rw [hKV] at ht
  have htwo : 2 ≤ K.relIndex E := by omega
  have he : E.relIndex V=1 := by nlinarith
  exact le_antisymm hEV (relIndex_eq_one.mp he)

include s in
/-- On the whole cover, equal small critical commutators determine the
literal seed kernels, including their full central attachments. -/
theorem small_critical_equal_commutators_kernel
    (hc : DistanceTwo.CentralLayer d) {a z w : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) a w)
    (hp : (Q d.radical z).relIndex (Z d.radical a)<4)
    (hq : (Q d.radical w).relIndex (Z d.radical a)<4)
    (heq : ⁅Z d.radical a,Z d.radical z⁆ = ⁅Z d.radical a,Z d.radical w⁆) :
    Z d.radical a ⊓ Q d.radical z = Z d.radical a ⊓ Q d.radical w := by
  have step {v v' : Vertex d.radical}
      (r : CriticalPath d.radical (replacementGeometry h d) a v)
      (t : CriticalPath d.radical (replacementGeometry h d) a v')
      (hr : (Q d.radical v).relIndex (Z d.radical a)<4)
      (ht : (Q d.radical v').relIndex (Z d.radical a)<4)
      (he : ⁅Z d.radical a,Z d.radical v⁆ = ⁅Z d.radical a,Z d.radical v'⁆) :
      Z d.radical a ⊓ Q d.radical v ≤ Q d.radical v' := by
    let rev := CriticalPath.ofPair (geometry := replacementGeometry h d) r.end_color
      (critical_reverse_pair s hc r)
    have hi : (Q d.radical a).relIndex (Z d.radical v)<4 := by
      rw [(small_critical_indices s hc r hr).2]
      decide
    have hJ := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a t.start_color
      (by rw [(replacementGeometry h d).distance_constant a t.start_color]
          exact replacementDistance_pos h d) t.critical
    have hmove : ⁅U d.radical a,Z d.radical v'⁆ ≤ ⁅Z d.radical v,Z d.radical a⁆ ⊔
        (stabilizer d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
      rw [small_critical_moving_commutator_eq s hc t ht,←he,commutator_comm (Z d.radical a)]
      exact le_sup_left
    have hactor := small_critical_aligned_actor_le s hc rev hi (Z d.radical v') hJ hmove
    have hfix : Z d.radical v' ≤ centralizer
        (Z d.radical a ⊓ Q d.radical v : Set (FreeAmalgam d.radical)) :=
      hactor.trans (sup_le
        ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical a r.start_color))).trans (centralizer_le inf_le_left))
        ((commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical v r.end_color)).trans (centralizer_le inf_le_right)))
    rw [←C_eq_Q s hc v' t.end_color]
    exact le_inf (inf_le_left.trans (Z_le_stabilizer_of_dist_le a _ t.critical.1.le))
      (le_centralizer_iff.mp hfix)
  exact le_antisymm (le_inf inf_le_left (step p q hp hq heq))
    (le_inf inf_le_left (step q p hq hp heq.symm))

private theorem index_two_commutator {F : Type*} [Group F]
    (V Q A Z : Subgroup F) [Finite V]
    (hA : A ≤ V) (hi : Q.relIndex V=2) (hne : ¬ A ≤ Q)
    (hQ : Q ≤ centralizer (Z : Set F)) (hN : V ≤ normalizer (Z : Set F)) :
    ⁅Z,A⁆ = ⁅Z,V⁆ := by
  have he := index_two_sup_kernel V Q A hA hi hne
  exact commutator_eq_of_centralizing_sup he
    (inf_le_right.trans hQ) (hA.trans hN)

include h in
private theorem radius_le_stabilizer_of_dist
    {a c : Vertex d.radical} (ha : color d.radical a=false)
    (hd : (cosetGraph d.radical).dist a c+2 ≤ replacementDistance h d) :
    V d.radical a ≤ stabilizer d.radical c := by
  apply (V_le_iff d.radical ha _).mpr
  intro w hw hwa
  apply Z_le_stabilizer_of_dist_le w _
  rw [(replacementGeometry h d).distance_constant w hw]
  have ht : (cosetGraph d.radical).dist w c ≤
      (cosetGraph d.radical).dist w a + (cosetGraph d.radical).dist a c :=
    (cosetGraph_connected d.radical).dist_triangle
  change _ ≤ replacementDistance h d
  omega

include e hz hn in
/-- At radius index two, the selected critical seed and its cubic conjugate
have identical nontrivial commutators whenever both escape the same core.
The common line is fixed by the whole intermediate stabilizer. -/
theorem nonsylow_paired_radius_two_common_line_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hi : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a)=2)
    (hout : ¬ Z d.radical (act d.radical q.cubic⁻¹ q.start) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))) :
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ =
      ⁅Z d.radical (act d.radical q.cubic⁻¹ q.start),Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ∧
    ⁅Z d.radical q.start,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have hac : (cosetGraph d.radical).dist a c+2 = replacementDistance h d := by
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
      (adjacent_symm d.radical q.adjacent_start))
    have ht : (cosetGraph d.radical).dist q.start a ≤
        (cosetGraph d.radical).dist q.start q.edge + (cosetGraph d.radical).dist q.edge a :=
      (cosetGraph_connected d.radical).dist_triangle
    simpa only [h₁,h₂] using ht
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hVG := radius_le_stabilizer_of_dist (h := h) p.start_color hac.le
  have hVQ := V_le_Q d.radical (geometry := replacementGeometry h d) p.start_color
    (show 2 < replacementDistance h d by omega)
  let := finite_stabilizer d.radical a
  let : Finite (V d.radical a) := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hx : q.cubic ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hVmap : (V d.radical a).map (MulAut.conj q.cubic).toMonoidHom = V d.radical a := by
    rw [←inv_inv q.cubic,←V_act]
    rw [show act d.radical q.cubic⁻¹ a=a from (stabilizer d.radical a).inv_mem hx]
  have hZV' : Z d.radical (act d.radical q.cubic⁻¹ q.start) ≤ V d.radical a := by
    rw [Z_act,inv_inv,←hVmap]
    exact map_mono hZV
  have hQC : Q d.radical c ≤ centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical c q.path.end_color))
  have heq : ⁅Z d.radical q.start,Z d.radical c⁆ =
      ⁅Z d.radical (act d.radical q.cubic⁻¹ q.start),Z d.radical c⁆ := by
    rw [commutator_comm (Z d.radical q.start),
      commutator_comm (Z d.radical (act d.radical q.cubic⁻¹ q.start))]
    exact (index_two_commutator _ _ _ _ hZV hi q.path.critical.2 hQC
      (hVG.trans (Z_normalized d.radical c))).trans
        (index_two_commutator _ _ _ _ hZV' hi hout hQC
          (hVG.trans (Z_normalized d.radical c))).symm
  refine ⟨heq,?_⟩
  have hline := nonsylow_paired_shift_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q
  have ht : color d.radical q.edge=true := by
    have hh := adjacent_color_ne d.radical q.adjacent_start
    rw [p.start_color] at hh
    cases he : color d.radical q.edge <;> simp_all
  have hZcQa : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.path.end_color)
    rw [(replacementGeometry h d).distance_constant c q.path.end_color,SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist a c < replacementDistance h d
    omega
  have hQmap : (Q d.radical a).map (MulAut.conj q.cubic).toMonoidHom=Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((Q_normalized d.radical a) hx)
  have hZcEdge : Z d.radical c ≤ Q d.radical (act d.radical q.cubic⁻¹ q.edge) := by
    rw [Q_act,inv_inv]
    exact hZcQa.trans (hQmap ▸ map_mono (Q_le_adjacent_h d.radical ht q.adjacent_start))
  obtain ⟨u,hfull⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,hfull]
  have hEdge := cube_edge_seed_commutator_le s hc u hR
    ((action_preserves_color d.radical _ _).trans q.path.start_color)
    ((adjacent_act_iff d.radical q.cubic⁻¹ _ _).mpr q.adjacent_shift)
  have hlineEdge : ⁅Z d.radical q.start,Z d.radical c⁆ ≤
      Z d.radical (act d.radical q.cubic⁻¹ q.edge) := by
    rw [heq]
    exact (commutator_mono le_rfl hZcEdge).trans hEdge
  have hfixed : ⁅Z d.radical q.start,Z d.radical c⁆ ≤ centralizer
      (Q d.radical (act d.radical q.cubic⁻¹ q.edge) : Set (FreeAmalgam d.radical)) := by
    intro v hv
    have hh := hlineEdge hv
    rw [Z,if_neg (by rw [action_preserves_color,ht]; decide)] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  apply le_centralizer_iff.mpr
  rw [←q.kernel_generation]
  apply sup_le (le_centralizer_iff.mp hline.2.2.2.1)
  have hh := le_centralizer_iff.mp hfixed
  rwa [Q_act,inv_inv] at hh

include e hz hn in
/-- The literal seed kernel is contained in the core conjugated by the
same selected cubic. Both the trapped and escaping conjugate-seed cases
are discharged; no additional centrality premise is imposed. -/
theorem nonsylow_paired_radius_two_conjugate_kernel_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hi : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a)=2) :
    Z d.radical q.start ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (act d.radical q.cubic (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  let w := act d.radical q.cubic⁻¹ q.start
  have hcancel : act d.radical q.cubic w=q.start := by
    dsimp only [w]
    rw [←act_mul,inv_mul_cancel,act_one]
  by_cases hout : Z d.radical w ≤ Q d.radical c
  · have hh := map_mono (f := (MulAut.conj q.cubic⁻¹).toMonoidHom) hout
    rw [←Z_act,←Q_act,hcancel] at hh
    exact inf_le_left.trans hh
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hline := nonsylow_paired_radius_two_common_line_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q hi hout
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have hac : (cosetGraph d.radical).dist a c+2 = replacementDistance h d := by
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
      (adjacent_symm d.radical q.adjacent_start))
    have ht : (cosetGraph d.radical).dist q.start a ≤
        (cosetGraph d.radical).dist q.start q.edge + (cosetGraph d.radical).dist q.edge a :=
      (cosetGraph_connected d.radical).dist_triangle
    simpa only [h₁,h₂] using ht
  have hx : q.cubic ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hwa : (cosetGraph d.radical).dist w a ≤ 2 := by
    conv_lhs => rhs; rw [←show act d.radical q.cubic⁻¹ a=a from (stabilizer d.radical a).inv_mem hx]
    rw [show w=act d.radical q.cubic⁻¹ q.start from rfl,dist_act]
    exact hnear
  have hw : color d.radical w=false :=
    (action_preserves_color d.radical _ _).trans q.path.start_color
  have hpair : CriticalPair d.radical w c ((replacementGeometry h d).exists_critical w hw) := by
    refine ⟨?_,hout⟩
    apply le_antisymm _ (criticalDistance_le d.radical w _ hout)
    rw [(replacementGeometry h d).distance_constant w hw]
    have ht : (cosetGraph d.radical).dist w c ≤
        (cosetGraph d.radical).dist w a + (cosetGraph d.radical).dist a c :=
      (cosetGraph_connected d.radical).dist_triangle
    change _ ≤ replacementDistance h d
    omega
  let r := CriticalPath.ofPair (geometry := replacementGeometry h d) hw hpair
  obtain ⟨t⟩ : Nonempty (CriticalPath d.radical (replacementGeometry h d) q.start
      (act d.radical q.cubic c)) := by
    rw [←hcancel]
    exact ⟨r.act q.cubic⟩
  let H := ⁅Z d.radical q.start,Z d.radical c⁆
  have hHmap : H.map (MulAut.conj q.cubic⁻¹).toMonoidHom=H :=
    mem_normalizer_iff_map_conj_eq.mp
      (((le_centralizer_iff.mp hline.2).trans (Subgroup.centralizer_le_normalizer _))
        ((stabilizer d.radical a).inv_mem hx))
  have heq : ⁅Z d.radical q.start,Z d.radical c⁆ =
      ⁅Z d.radical q.start,Z d.radical (act d.radical q.cubic c)⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj q.cubic⁻¹).toMonoidHom) hline.1
    change H.map (MulAut.conj q.cubic⁻¹).toMonoidHom = _ at hh
    rw [hHmap,map_commutator,←Z_act,←Z_act,hcancel] at hh
    exact hh
  have hp : (Q d.radical c).relIndex (Z d.radical q.start)<4 := by
    rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns q.path).1]
    decide
  have ht : (Q d.radical (act d.radical q.cubic c)).relIndex (Z d.radical q.start)<4 := by
    rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns t).1]
    decide
  exact (small_critical_equal_commutators_kernel s hc q.path t hp ht heq).le.trans inf_le_right

include e hz hn in
private theorem paired_radius_two_control_false
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : PairedBackwardShift (h := h) p)
    (hi : (Q d.radical (p.walk.getVert (p.walk.length-2))).relIndex (V d.radical a)=2)
    (hcontrol : ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),Z d.radical a'⁆ ≤
      Z d.radical a) : False := by
  let c := p.walk.getVert (p.walk.length-2)
  let K := Z d.radical q.start ⊓ Q d.radical c
  let Y := K ⊔ Z d.radical a
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hb2 : 2 < replacementDistance h d := by omega
  have hnear : (cosetGraph d.radical).dist q.start a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr q.adjacent_shift)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
      (adjacent_symm d.radical q.adjacent_start))
    have ht : (cosetGraph d.radical).dist q.start a ≤
        (cosetGraph d.radical).dist q.start q.edge + (cosetGraph d.radical).dist q.edge a :=
      (cosetGraph_connected d.radical).dist_triangle
    simpa only [h₁,h₂] using ht
  have hZV : Z d.radical q.start ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hnear)
  have hKV : K ≤ V d.radical a := inf_le_left.trans hZV
  have hYV : Y ≤ V d.radical a := sup_le hKV (Z_le_VBall d.radical _ 2)
  have hVG : V d.radical a ≤ stabilizer d.radical a :=
    (V_le_Q d.radical (geometry := replacementGeometry h d) p.start_color hb2).trans (fun _ hx => hx.1)
  have hline := nonsylow_paired_shift_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q
  have hsmall : (Q d.radical c).relIndex (Z d.radical q.start)<4 := by
    rw [(nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns q.path).1]
    decide
  have hKN : Q d.radical q.edge ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
    have hh := (small_critical_kernel_normalized_iff_first_seed s hc q.path hsmall).mpr
      (q.first.symm ▸ hline.2.1)
    simpa only [q.first] using hh
  have hKG : K ≤ stabilizer d.radical a := hKV.trans hVG
  have hKmove : ⁅K,Z d.radical a'⁆ ≤ Z d.radical a :=
    (commutator_mono (le_inf hKV inf_le_right) le_rfl).trans hcontrol
  have hx : q.cubic ∈ stabilizer d.radical a := Ltilde_le_stabilizer _ q.cubic_mem
  have hZmap : (Z d.radical a).map (MulAut.conj q.cubic⁻¹).toMonoidHom=Z d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized d.radical a) ((stabilizer d.radical a).inv_mem hx))
  have hVmap : (V d.radical a).map (MulAut.conj q.cubic⁻¹).toMonoidHom=V d.radical a := by
    rw [←V_act,show act d.radical q.cubic a=a from hx]
  have hKother := nonsylow_paired_radius_two_conjugate_kernel_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p q hi
  have hKmove' : ⁅K,Z d.radical (act d.radical q.cubic a')⁆ ≤ Z d.radical a := by
    have hm := map_mono (f := (MulAut.conj q.cubic⁻¹).toMonoidHom) hcontrol
    rw [map_commutator,map_inf _ _ _ (MulAut.conj q.cubic⁻¹).injective,hVmap,←Q_act,←Z_act,hZmap] at hm
    exact (commutator_mono (le_inf hKV hKother) le_rfl).trans hm
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hA'G : Z d.radical (act d.radical q.cubic a') ≤ stabilizer d.radical a := by
    have hm := map_mono (f := (MulAut.conj q.cubic⁻¹).toMonoidHom) hAG
    rw [←Z_act,←stabilizer_act,show act d.radical q.cubic a=a from hx] at hm
    exact hm
  have hYmove (A : Subgroup (FreeAmalgam d.radical))
      (hA : A ≤ stabilizer d.radical a) (hK : ⁅K,A⁆ ≤ Z d.radical a) :
      ⁅Y,A⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      K (Z d.radical a) A (Z d.radical a) (Z_normalized d.radical a)
      hKG (Z_le_stabilizer d.radical a) hK
    exact le_normalizer_iff_commutator_le_left.mp (hA.trans (Z_normalized d.radical a))
  have hYN : stabilizer d.radical a ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    rw [←q.endpoint_generation]
    refine sup_le (sup_le ?_ ?_) ?_
    · apply le_trans (le_inf hKN _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      exact (show Q d.radical q.edge ≤ stabilizer d.radical a from
        fun _ hx => hx.2 _ (adjacent_symm d.radical q.adjacent_start)).trans (Z_normalized d.radical a)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hAG hKmove).trans le_sup_right)
    · exact le_normalizer_iff_commutator_le_left.mpr ((hYmove _ hA'G hKmove').trans le_sup_right)
  have hKB : K ≤ B d.radical a ((replacementGeometry h d).Z_normal _) :=
    le_sup_left.trans (normalized_radius_le_slice_of_actor_at s hb2 p.start_color Y (Z d.radical a')
      hYV hYN hAG (critical_reverse_pair s hc p).2 (hYmove _ hAG hKmove))
  have hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) := by
    have hBmap : (B d.radical a ((replacementGeometry h d).Z_normal _)).map
        (MulAut.conj q.transporter⁻¹).toMonoidHom = B d.radical a ((replacementGeometry h d).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb2 a p.start_color
        ((stabilizer d.radical a).inv_mem q.transporter_mem))
    rw [←q.start_eq,U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj q.transporter⁻¹).injective]
    exact nonsylow_forward_slice_strict_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p
  let := finite_Z d.radical q.start
  let : Finite (U d.radical q.start) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical q.start)) (inclusion_injective _)
  have hupper : (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical q.start) ≤ 2 := by
    have hh := (relIndex_le_of_le_left hKB (L := U d.radical q.start) index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (H := K) (DistanceEight.U_le_Z d.radical q.start) index_ne_zero_of_finite)
    have hidx : K.relIndex (Z d.radical q.start)=2 := by
      dsimp only [K]
      rw [inf_relIndex_left]
      exact (nonsylow_critical_indices_two_knownSimple (e := e) (hz := hz) (hn := hn) hb hns q.path).1
    exact hh.trans_eq hidx
  exact (Nat.not_le_of_gt hstrict) hupper

include e hz hn in
/-- The exact radius-index-four tower is impossible on a path with the
actual generating interior kernels. This is the strict-growth step of (5.11). -/
theorem nonsylow_generated_radius_ne_four_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ Q d.radical (p.walk.getVert 3) =
      stabilizer d.radical (p.walk.getVert 2)) :
    (Q d.radical a).relIndex (V d.radical a') ≠ 4 := by
  intro hfour
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let rev : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  have hl : p.walk.length=replacementDistance h d := p.length_eq_b
  have he : rev.walk.getVert (rev.walk.length-2)=p.walk.getVert 2 := by
    dsimp only [rev]
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse]
    congr 1
    omega
  have ht := nonsylow_radius_four_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hgen hfour
  have hcomm := nonsylow_radius_four_kernel_commutator_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns p hgen hfour
  obtain ⟨q⟩ := nonsylow_paired_backward_shift_knownSimple (e := e) (hz := hz) (hn := hn) hb hns rev
  apply paired_radius_two_control_false (e := e) (hz := hz) (hn := hn) hb hns rev q
  · simpa only [he] using ht.1
  · rw [he,hcomm,commutator_comm]
    exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_right).trans
      (DistanceEight.U_le_Z d.radical a')

include e hz hn in
/-- Every minimum characteristic replacement of an original nonsylow
radical has critical distance at most four. All index, conjugate-kernel,
and strict-slice premises are discharged on the original graph. -/
theorem nonsylow_replacementDistance_le_four_knownSimple
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R)) :
    replacementDistance h d ≤ 4 := by
  by_contra! hb
  obtain ⟨a,a',p,hgen,hfour,_⟩ := nonsylow_four_lt_exists_radius_kernel_tower_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  exact nonsylow_generated_radius_ne_four_knownSimple (e := e) (hz := hz) (hn := hn) hb hns p hgen hfour

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
