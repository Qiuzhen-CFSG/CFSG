module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.GeneratingShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport

/-!
# Restricted kernels and opposite movers on the original Borel graph

On three actual generating backward shifts, let K be the full last critical
kernel and N its join with the intermediate seed. The strict forward bound
makes K escape the intermediate Baumann slice. The proper Thompson mover
normalizes N, and the full reverse omega kernel normalizes K. The intermediate
two-residual cannot normalize N: its section has order dividing eight, so the
component's genuine A6 quotient would put it in the Baumann slice.

Consequently endpoint normalization forces the opposite mover to contain the
intermediate core; under central generation it also forces equality of the
movers. Failure of endpoint normalization instead gives a nonzero restricted
commutator of order two and central generation of full omega at every vertex.
The edge intersection of its span with the last critical line is exactly the
central part of that span at the last start, and is central at the two preceding
starts as well. Its intersection with the last critical line is trivial.

All subgroups and transporters belong to the original exceptional graph. The
cubic projection retains its kernel E with odd quotient E/Q, and both full
moving covers retain their central attachments. OriginalSylowExceptional
constructs this configuration on the literal original c.L,d.S source. The
nonnormalizing alternative, the remaining mover comparison and the terminal
distance exclusions still need to be discharged before whole-core exhaustion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3), (5.9)--(5.10), printed pp.866--867,921--923.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h in
private theorem terminal_last_edge_inputs {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) (hb : 2 < sourceDistance h) :
    Adjacent Rg z (p.walk.getVert (p.walk.length-1)) ∧
    Q Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg (p.walk.getVert (p.walk.length-1)) ∧
    Q Rg (p.walk.getVert (p.walk.length-2)) ≤ stabilizer Rg z := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hadj : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  have ht : color Rg (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne Rg hadj
    rw [p.end_color] at hh
    cases he : color Rg (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hprev : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hle := Q_le_adjacent_h Rg ht hprev
  exact ⟨hadj,hle,hle.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hadj))⟩

omit [Finite G] in
private theorem terminal_neighbor_seed_radius {a c t : Vertex Rg}
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) : Z Rg c ≤ V Rg a := by
  have hdist : (cosetGraph Rg).dist c a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj Rg _ _).mpr hct)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat))
    have hh := (cosetGraph_connected Rg).dist_triangle (u := c) (v := t) (w := a)
    omega
  exact (Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hdist)

include h e hz hk in
/-- Failure of endpoint normalization makes the restricted kernel displacement
an order-two subgroup of the same restricted seed. -/
theorem borel_restricted_kernel_line
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 Y]
    (hYV : Y ≤ V Rg a)
    (htrap : Y ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hYN : Z Rg z ⊓ Q Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)))
    (hnorm : ¬ Z Rg z ≤ normalizer
      ((Y ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    Nat.card (⁅Y,Z Rg z ⊓ Q Rg a⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅Y,Z Rg z ⊓ Q Rg a⁆ ≤ Y := by
  let F := Z Rg z ⊓ Q Rg a
  let K := ⁅Y,F⁆
  have hb2 : 2 < sourceDistance h := by omega
  have hYQ : Y ≤ Q Rg a := hYV.trans ((sourceGeometry h).V_le_Q hb2 a p.start_color)
  have hYG : Y ≤ stabilizer Rg z := htrap.trans (terminal_last_edge_inputs h p hb2).2.2
  have hKG : K ≤ Y := le_normalizer_iff_commutator_le_left.mp hYN
  have hcrit : ⁅Z Rg a,Z Rg z⁆ ≤ Z Rg a := critical_seed_commutator_le h p
  have contradiction_of_control (hcontrol : ⁅Y,Z Rg z⁆ ≤ Z Rg a ⊔ K) : False := by
    apply hnorm
    have hZnorm : Z Rg z ≤ normalizer (Z Rg a : Set (FreeAmalgam Rg)) :=
      le_normalizer_iff_commutator_le_left.mpr hcrit
    apply le_normalizer_iff.mpr
    intro x hx v hv
    have hm : (Y ⊔ Z Rg a).map (MulAut.conj x).toMonoidHom ≤ Y ⊔ Z Rg a := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hZnorm hx)).le.trans le_sup_right)
      rintro _ ⟨y,hy,rfl⟩
      have hh := (Y ⊔ Z Rg a).mul_mem
        ((hcontrol.trans (sup_le le_sup_right (hKG.trans le_sup_left)))
          (by rw [commutator_comm]; exact commutator_mem_commutator hx hy))
        (mem_sup_left hy)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
  have hbound : Nat.card K ≤ 2 := by
    rcases borel_elementary_reverse_kernel_control_or_card h e hz hk u hR p hp Y htrap hYQ with hc | hc
    · change ⁅Y,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅F,Y⁆ at hc
      rw [commutator_comm F Y] at hc
      exact (contradiction_of_control hc).elim
    · change Nat.card (⁅Y,F⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2
      rw [commutator_comm]
      exact hc
  have hne : K ≠ ⊥ := by
    intro hzero
    have hc := small_critical_kernel_commutator h e hz hk p hp Y hYG
      (commutator_eq_bot_iff_le_centralizer.mp hzero)
    exact contradiction_of_control (hc.trans (hcrit.trans le_sup_left))
  let := finite_stabilizer Rg a
  let : Finite Y := Finite.of_injective
    (inclusion (hYV.trans ((sourceGeometry h).V_local a p.start_color (by
      rw [(sourceGeometry h).distance_constant a p.start_color]; exact hb2)))) (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKG) (inclusion_injective _)
  have hpos : 1 < Nat.card K := (one_lt_card_iff_ne_bot K).mpr hne
  exact ⟨by change Nat.card K = 2; omega,hKG⟩

omit [Finite G] in
private theorem terminal_edge_seed_central {t : Vertex Rg} (ht : color Rg t = true) :
    Z Rg t ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
  intro x hx
  rw [Z,if_neg (by simp [ht])] at hx
  exact (mem_omegaCenter_iff.mp hx).2.2

omit [Finite G] in
private theorem terminal_fixed_map (A H : Subgroup (FreeAmalgam Rg))
    (hc : A ≤ centralizer (H : Set (FreeAmalgam Rg)))
    {x : FreeAmalgam Rg} (hx : x ∈ H) :
    A.map (MulAut.conj x).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hc hx))

/-- Two generating edges and the same shift transporter make the opposite
radius's edge intersection central at all three starting vertices. -/
theorem borel_three_shift_radius_intersection_central
    (hb : 4 < sourceDistance h)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let I := V Rg z ⊓ Z Rg t.edge
    I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) ∧
    I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) ∧
    I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let w := p.walk.getVert (p.walk.length-2)
  let I := V Rg z ⊓ Z Rg t.edge
  have hb2 : 2 < sourceDistance h := by omega
  have htz : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge
    · exact (hh he.symm).elim
    · rfl
  have hrz : color Rg r.edge = true := by
    have hh := adjacent_color_ne Rg r.adjacent_start
    rw [q.path.start_color] at hh
    cases he : color Rg r.edge
    · exact (hh he.symm).elim
    · rfl
  have hVQ : V Rg z ≤ Q Rg z :=
    V_le_Q Rg (geometry := sourceGeometry h) r.path.end_color hb2
  have hVQw : V Rg z ≤ Q Rg w := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) r.path.end_color
    rw [q.path.dist_end]
    have hl := q.path.length_eq_b
    change q.path.walk.length-(q.path.walk.length-2)+2 < sourceDistance h
    omega
  have hCz : V Rg z ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    hVQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z r.path.end_color)))
  have hCw : V Rg z ≤ centralizer (Z Rg w : Set (FreeAmalgam Rg)) :=
    hVQw.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg w q.path.end_color)))
  have hIr : I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←t.generation]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (terminal_edge_seed_central htz)))
      (le_centralizer_iff.mp (inf_le_left.trans hCz))
  have hIedge : I ≤ Z Rg r.edge := by
    obtain ⟨x,hx,hxe⟩ := stabilizer_transitive_neighbors Rg r.start
      t.adjacent_start r.adjacent_shift
    rw [←hxe,Z_act,←terminal_fixed_map I (stabilizer Rg r.start) hIr
      ((stabilizer Rg r.start).inv_mem hx)]
    exact map_mono inf_le_right
  have hIq : I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←r.generation]
    exact sup_le (le_centralizer_iff.mp (hIedge.trans (terminal_edge_seed_central hrz)))
      (le_centralizer_iff.mp (inf_le_left.trans hCw))
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hshift : act Rg t.transporter q.start = t.start := by
    simpa only [hr2] using t.start_eq
  have hIt : I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
    rw [←hshift,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj t.transporter⁻¹).toMonoidHom) hIq).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [terminal_fixed_map I (stabilizer Rg r.start) hIr
      ((stabilizer Rg r.start).inv_mem t.transporter_mem)] at hh
  exact ⟨hIr,hIq,hIt⟩


include h e hz hk in
/-- The proper Thompson mover fixes a small critical line and normalizes
its full critical kernel on the original Borel edge. -/
theorem borel_small_mover_normalizes_critical_kernel
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    edgeOffenderJoin a (p.walk.getVert 1) ≤
      centralizer ((⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
    edgeOffenderJoin a (p.walk.getVert 1) ≤
      normalizer ((Z Rg a ⊓ Q Rg z : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hadj : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨J,_,hJ,hQJ,hJT,_,_,_,hquad⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR p.start_color hadj
  have hAG : Z Rg z ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg z ((sourceGeometry h).exists_critical z p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant _ p.end_color]
    change p.walk.length-1 < sourceDistance h
    omega
  have hAJ : Z Rg z ≤ J := by
    rw [←hJ]
    apply borel_small_commutator_actor_le_mover h e hz hk u hR p.start_color hadj _ hAG
    rw [small_critical_moving_commutator_eq h e hz hk p hp,
      small_critical_commutator_card h e hz hk p hp]
  have hfix : J ≤ centralizer ((⁅Z Rg a,Z Rg z⁆ :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [←small_critical_moving_commutator_eq h e hz hk p hp]
    exact (commutator_mono (commutator_mono le_rfl hAJ) le_rfl).trans_eq hquad
  have hJG : J ≤ stabilizer Rg a :=
    hJT.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hadj))
  have hnorm : J ≤ normalizer (Z Rg a ⊓ Q Rg z : Set (FreeAmalgam Rg)) := by
    have hh := le_inf hJG hfix
    rw [←small_critical_kernel_normalizer_eq_line_centralizer h e hz hk p hp] at hh
    exact hh.trans inf_le_right
  rw [hJ]
  exact ⟨hfix,hnorm⟩

include h e hz hk in
/-- The full restricted kernel on three actual shifts has index two and
escapes the intermediate Baumann slice. Both its own small mover and the
full reverse omega kernel normalize it. If the preceding endpoint fails
to normalize its join with the intermediate seed, its displacement is a
line and full omega is centrally generated at every component vertex. -/
theorem borel_three_shift_restricted_kernel
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z Rg t.start ⊓ Q Rg v
    let N := K ⊔ Z Rg r.start
    K.relIndex (Z Rg t.start) = 2 ∧
    (¬ K ≤ B Rg r.start ((sourceGeometry h).Z_normal _)) ∧
    edgeOffenderJoin t.start t.edge ≤ normalizer (N : Set (FreeAmalgam Rg)) ∧
    X Rg z ⊓ Q Rg r.start ≤ normalizer (K : Set (FreeAmalgam Rg)) ∧
    ((¬ Z Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))) →
      Nat.card (⁅K,Z Rg z ⊓ Q Rg r.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      ⁅K,Z Rg z ⊓ Q Rg r.start⁆ ≤ K ∧
      ∀ w : Vertex Rg, color Rg w = false →
        X Rg w = U Rg w ⊔
          (X Rg w ⊓ centralizer (stabilizer Rg w : Set (FreeAmalgam Rg))) ∧
        X Rg w = Z Rg w) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let N := K ⊔ Z Rg r.start
  have hb2 : 2 < sourceDistance h := by omega
  have hr := two_borel_backward_shifts_small_moving h e hz hk hb p q r
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hrs : (Q Rg z).relIndex (Z Rg r.start) < 4 := by rw [hr.2.1]; decide
  have hts : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hki : K.relIndex (Z Rg t.start) = 2 := by
    rw [show K = Z Rg t.start ⊓ Q Rg v from rfl,inf_relIndex_left]
    exact ht.2.1
  have hstrict : 2 < (B Rg r.start ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg t.start) := by
    have hh := borel_forward_slice_strict_at h e hz hk hb u hR r.path
    have hm : (B Rg r.start ((sourceGeometry h).Z_normal _)).map
        (MulAut.conj t.transporter⁻¹).toMonoidHom =
          B Rg r.start ((sourceGeometry h).Z_normal _) :=
      mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
        hb2 r.start r.path.start_color ((stabilizer Rg r.start).inv_mem t.transporter_mem))
    rw [←t.start_eq,U_act,←hm,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hh
  let := finite_Z Rg t.start
  have hnot : ¬ K ≤ B Rg r.start ((sourceGeometry h).Z_normal _) := by
    intro hKB
    have hi : (B Rg r.start ((sourceGeometry h).Z_normal _)).relIndex (Z Rg t.start) ≤ 2 :=
      (relIndex_le_of_le_left hKB index_ne_zero_of_finite).trans_eq hki
    have hj := relIndex_le_of_le_right (H := B Rg r.start ((sourceGeometry h).Z_normal _))
      (DistanceEight.U_le_Z Rg t.start) index_ne_zero_of_finite
    exact (Nat.not_le_of_gt hstrict) (hj.trans hi)
  have hEK := (borel_small_mover_normalizes_critical_kernel h e hz hk u hR t.path hts).2
  rw [t.first] at hEK
  obtain ⟨E,_,hE,_,hET,_,_,_,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR t.path.start_color t.adjacent_shift
  have hTa : Q Rg t.edge ≤ stabilizer Rg r.start :=
    fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_start)
  have hEN : edgeOffenderJoin t.start t.edge ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hEK (((hE.le.trans hET).trans hTa).trans (Z_normalized Rg r.start))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hzv : (cosetGraph Rg).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    omega
  have hXG : X Rg z ⊓ Q Rg r.start ≤ stabilizer Rg t.start :=
    (inf_le_right.trans (Q_le_adjacent_h Rg htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift))
  have hXv : X Rg z ⊓ Q Rg r.start ≤ stabilizer Rg v :=
    ((inf_le_left.trans (omegaCenter_le (Q Rg z))).trans
      (Q_le_stabilizer_of_dist_two Rg z v r.path.end_color hzv))
  have hNK : X Rg z ⊓ Q Rg r.start ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    (le_inf (hXG.trans (Z_normalized Rg t.start))
      (hXv.trans (Q_normalized Rg v))).trans inf_normalizer_le_normalizer_inf
  have hZV : Z Rg t.start ≤ V Rg r.start :=
    terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift
  have hKQ : K ≤ Q Rg r.start :=
    (inf_le_left.trans hZV).trans ((sourceGeometry h).V_le_Q hb2 r.start r.path.start_color)
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z r.path.end_color (by
    rw [(sourceGeometry h).distance_constant z r.path.end_color]; exact sourceDistance_pos h)
  refine ⟨hki,hnot,hEN,hNK,?_⟩
  intro hnZ
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.of_le inf_le_left
  have hline := borel_restricted_kernel_line h e hz hk hb u hR r.path hrs K
    (inf_le_left.trans hZV) inf_le_right ((inf_le_inf_right _ hZX).trans hNK) hnZ
  refine ⟨hline.1,hline.2,?_⟩
  have hKG : K ≤ stabilizer Rg z := inf_le_right.trans (terminal_last_edge_inputs h r.path hb2).2.2
  let pr : CriticalPath Rg (sourceGeometry h) z r.start :=
    CriticalPath.ofPair r.path.end_color (reverse_pair h e r.path)
  have hs : (Q Rg r.start).relIndex (Z Rg z) < 4 := by rw [hr.2.2.1]; decide
  have hgen : X Rg z = U Rg z ⊔
      (X Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) := by
    rcases small_critical_omega_generation_or_control_at h e hz hk pr hs with hh | hc
    · exact hh
    apply False.elim
    apply hnZ
    have hXN : X Rg z ≤ normalizer (Z Rg r.start : Set (FreeAmalgam Rg)) :=
      (critical_X_le_vertex h e z r.path.end_color r.start pr.critical).trans
        (Z_normalized Rg r.start)
    have hRZ : ⁅X Rg z,Z Rg r.start⁆ ≤ Z Rg r.start := le_normalizer_iff_commutator_le_right.mp hXN
    have hKR : K ≤ centralizer ((⁅X Rg z,Z Rg r.start⁆ :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      (hKQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg r.start r.path.start_color)))).trans (centralizer_le hRZ)
    have hbound : ⁅X Rg z,K⁆ ≤ N := by
      rw [commutator_comm]
      exact (hc K hKG hKR).trans (sup_le (hRZ.trans le_sup_right)
        ((le_normalizer_iff_commutator_le_left.mp hNK).trans le_sup_left))
    have hnormX : X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
      apply le_normalizer_iff.mpr
      intro x hx y hy
      have hm : N.map (MulAut.conj x).toMonoidHom ≤ N := by
        rw [show N = K ⊔ Z Rg r.start from rfl,Subgroup.map_sup]
        refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
        rintro _ ⟨k,hkK,rfl⟩
        have hh := N.mul_mem (hbound (commutator_mem_commutator hx hkK)) (mem_sup_left hkK)
        simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
      exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hy)
    exact hZX.trans hnormX
  intro w hw
  have hwgen := omega_generation_transport r.path.end_color hw hgen
  exact ⟨hwgen,omega_eq_seed_of_central_generation h w hw hwgen⟩

include h e hz hk in
private theorem terminal_residual_small_radius_le_slice
    {a : Vertex Rg} (ha : color Rg a = false)
    (D : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg a)
    (hDN : Ltilde Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hsmall : (Z Rg a).relIndex D ∣ 8) :
    D ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg ha
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj g).toMonoidHom
  have hV : (V Rg a).map f = V Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (V_act Rg g⁻¹ a).symm
  have hL : (Ltilde Rg a).map f = Ltilde Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (Ltilde_act Rg g⁻¹ a).symm
  have hZ : (Z Rg a).map f = Z Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (Z_act Rg g⁻¹ a).symm
  have hDV₀ : D.map f ≤ V Rg (alpha Rg) := (map_mono hDV).trans_eq hV
  have hDN₀ : Ltilde Rg (alpha Rg) ≤ normalizer (D.map f : Set (FreeAmalgam Rg)) := by
    rw [←hL]
    exact (map_mono hDN).trans (le_normalizer_map f)
  have hi : (Z Rg (alpha Rg)).relIndex (D.map f) ∣ 8 := by
    rw [←hZ,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hsmall
  have hh := residual_small_radius_le_slice h e hz hk (D.map f) hDV₀ hDN₀ hi
  have hB : (B Rg a ((sourceGeometry h).Z_normal _)).map f =
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    simpa only [inv_inv,hbase] using
      (Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h)
        (distance_gt_two h e hz hk) g⁻¹ a ha).symm
  rw [←hB] at hh
  exact (map_le_map_iff_of_injective (MulAut.conj g).injective).mp hh

include h e hz hk in
/-- Endpoint normalization forces the opposite proper mover to contain the
intermediate core. If full omega is centrally generated the two movers
coincide. This is the literal restricted-kernel comparison of (5.10). -/
theorem borel_three_shift_mover_comparison
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let N := (Z Rg t.start ⊓ Q Rg v) ⊔ Z Rg r.start
    (¬ Ltilde Rg r.start ≤ normalizer (N : Set (FreeAmalgam Rg))) ∧
    (Z Rg z ≤ normalizer (N : Set (FreeAmalgam Rg)) →
      Q Rg r.start ≤ edgeOffenderJoin t.start t.edge ∧
      (X Rg r.start = U Rg r.start ⊔
        (X Rg r.start ⊓ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg))) →
        edgeOffenderJoin r.start t.edge = edgeOffenderJoin t.start t.edge)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let N := K ⊔ Z Rg r.start
  have hb2 : 2 < sourceDistance h := by omega
  have hkern := borel_three_shift_restricted_kernel h e hz hk hb u hR p q r t
  have hZV := terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift
  have hNV : N ≤ V Rg r.start :=
    sup_le (inf_le_left.trans hZV) (Z_le_VBall Rg r.start 2)
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hZaX : Z Rg r.start ≤ X Rg r.start :=
    (sourceGeometry h).omega_bound _ r.path.start_color (by
      rw [(sourceGeometry h).distance_constant _ r.path.start_color]; exact sourceDistance_pos h)
  have hZaT : Z Rg r.start ≤ Q Rg t.edge :=
    (hZaX.trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg htcol t.adjacent_start)
  have hTN : Q Rg t.edge ≤ normalizer (Z Rg t.start : Set (FreeAmalgam Rg)) :=
    (show Q Rg t.edge ≤ stabilizer Rg t.start from
      fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift)).trans (Z_normalized Rg t.start)
  let := finite_Z Rg r.start
  have hbig : (Z Rg r.start).relIndex (Z Rg t.start ⊔ Z Rg r.start) ∣ 8 := by
    rw [relIndex_sup_of_normalizes (Z Rg t.start) (Z Rg r.start) (hZaT.trans hTN)]
    have hd := relIndex_dvd_of_le_left (Z Rg t.start)
      (adjacent_Z_le Rg r.path.start_color t.adjacent_start)
    rw [borel_full_seed_edge_index h e hz hk u hR t.path.start_color t.adjacent_shift] at hd
    exact hd
  have hsmall : (Z Rg r.start).relIndex N ∣ 8 := by
    have hm := relIndex_mul_relIndex (Z Rg r.start) N
      (Z Rg t.start ⊔ Z Rg r.start) le_sup_right (sup_le_sup_right inf_le_left _)
    exact (Dvd.intro _ hm).trans hbig
  have hnot : ¬ Ltilde Rg r.start ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    intro hn
    exact hkern.2.1 (le_sup_left.trans
      (terminal_residual_small_radius_le_slice h e hz hk r.path.start_color N hNV hn hsmall))
  refine ⟨hnot,?_⟩
  intro hnZ
  have hcore : Q Rg r.start ≤ edgeOffenderJoin t.start t.edge := by
    by_contra hnQ
    have hres := (borel_opposite_generation_of_core_not_le h e hz hk u hR
      r.path.start_color t.path.start_color t.adjacent_start t.adjacent_shift
      (Z Rg z) t.generation hnQ).2
    exact hnot (hres.trans (sup_le hkern.2.2.1 hnZ))
  refine ⟨hcore,?_⟩
  intro hgen
  by_contra hne
  exact borel_opposite_containing_core_nonsplit h e hz hk u hR
    r.path.start_color t.path.start_color t.adjacent_start t.adjacent_shift hne hcore hgen

include h e hz hk in
/-- The edge intersection of the actual restricted-commutator span is
central in all three starting stabilizers. Its definition retains the full
restricted seed and the genuine reverse critical kernel. -/
theorem borel_three_shift_kernel_intersection_central
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z Rg t.start ⊓ Q Rg v,Z Rg z ⊓ Q Rg r.start⁆
    let D := ⁅Z Rg t.start,Z Rg v⁆
    let I := (H ⊔ D) ⊓ Z Rg t.edge
    H ⊔ D ≤ V Rg z ∧ H ⊔ D ≤ Z Rg t.start ∧
      I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) ∧
      I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) ∧
      I = (H ⊔ D) ⊓ centralizer
        (stabilizer Rg t.start : Set (FreeAmalgam Rg)) ∧
      D ⊓ I = ⊥ := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let F := Z Rg z ⊓ Q Rg r.start
  let H := ⁅K,F⁆
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let I := (H ⊔ D) ⊓ Z Rg t.edge
  have hb2 : 2 < sourceDistance h := by omega
  have hkern := borel_three_shift_restricted_kernel h e hz hk hb u hR p q r t
  have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z r.path.end_color (by
    rw [(sourceGeometry h).distance_constant z r.path.end_color]; exact sourceDistance_pos h)
  have hHK : H ≤ K := le_normalizer_iff_commutator_le_left.mp
    ((inf_le_inf_right _ hZX).trans hkern.2.2.2.1)
  have hKG : K ≤ stabilizer Rg z := inf_le_right.trans (terminal_last_edge_inputs h r.path hb2).2.2
  have hHz : H ≤ Z Rg z := (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp (hKG.trans (Z_normalized Rg z)))
  have hDz : D ≤ Z Rg v := by
    change ⁅Z Rg t.start,Z Rg v⁆ ≤ Z Rg v
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((Z_le_stabilizer_of_dist_le t.start _ t.path.critical.1.le).trans (Z_normalized Rg v))
  have hvz : (cosetGraph Rg).dist v z ≤ 2 := by
    rw [r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    change r.path.walk.length-(r.path.walk.length-2) ≤ 2
    omega
  have hV : H ⊔ D ≤ V Rg z := sup_le (hHz.trans (Z_le_VBall Rg z 2))
    (hDz.trans ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg hvz)))
  have hZ : H ⊔ D ≤ Z Rg t.start :=
    sup_le (hHK.trans inf_le_left) (critical_seed_commutator_le h t.path)
  have hc := borel_three_shift_radius_intersection_central h hb p q r t
  have hIrad : I ≤ V Rg z ⊓ Z Rg t.edge := inf_le_inf_right _ hV
  have hIr := hIrad.trans hc.1
  have hIq := hIrad.trans hc.2.1
  have hIt := hIrad.trans hc.2.2
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_shift
    rw [t.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hZQ : Z Rg t.start ≤ Q Rg t.start := Z_le_Q_of_dist_lt Rg t.start
    ((sourceGeometry h).exists_critical t.start t.path.start_color) (by
      rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant _ t.path.start_color]
      exact sourceDistance_pos h)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  have heq : I = (H ⊔ D) ⊓ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
    apply le_antisymm (le_inf inf_le_left hIt)
    intro x hx
    refine ⟨hx.1,?_⟩
    rw [Z,if_neg (by simp [htcol])]
    refine mem_omegaCenter_iff.mpr ⟨Q_le_adjacent_h Rg htcol t.adjacent_shift (hZQ (hZ hx.1)),
      elemPow_eq_one_of_isElementaryAbelian x (hZ hx.1),?_⟩
    intro y hy
    exact hx.2 y (hy.2 _ (adjacent_symm Rg t.adjacent_shift))
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hsmall : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hDI : D ⊓ I = ⊥ := le_bot_iff.mp
    ((inf_le_inf_left D hIt).trans_eq (small_critical_commutator_inf_centralizer h e hz hk t.path hsmall))
  exact ⟨hV,hZ,hIr,hIq,heq,hDI⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
