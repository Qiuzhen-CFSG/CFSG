module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.CriticalMidpoint
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardClosure
public import Theory.GroupTheory.Commutator.RelativeGeneration
/-!
# The selected backward kernel lies in the Baumann subgroup

For a coordinated backward critical path, let A be its starting Z-layer
intersected with the endpoint kernel. The selected first edge kernel normalizes
A. If the original critical image is large, the radius commutator bound gives
[A,Z_e] inside Z_alpha directly. If that image is small, the last edge bounds
[A,Z_e intersect Q_alpha] by the original critical line. The abelian point-core
image makes the selected edge kernel normalize this subgroup of order at most
two, hence centralize it. Local generation then makes it fixed in the moving
natural layer, so it is trivial. The predecessor-fixer result again gives
[A,Z_e] inside Z_alpha, and the normal radius bound places A in B_alpha.

Consequently a small selected backward image gives forward Baumann index at
most two. The native lower bound makes this exactly two for the prescribed
forward vertex. Its characteristic-replacement application is source (5.12)(3)
with the selected smallness premise supplied by the separate source (5.12)(2)
argument. No normalization alternative from (5.12)(1) is required here.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(3), printed pp.926--927,
using the native full point-core specialization of (3.3)(ii) and (5.2).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
private theorem fixed_mod_central_normalizes_commutator {G : Type*} [Group G]
    (A Q L : Subgroup G) (hAQ : A ≤ normalizer (Q : Set G))
    (hLQ : L ≤ normalizer (Q : Set G))
    (hLA : ⁅L,A⁆ ≤ centralizer (Q : Set G)) :
    L ≤ normalizer ((⁅A,Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a,ha,q,hq,rfl⟩
  have hq' : l*q*l⁻¹ ∈ Q := (mem_normalizer_iff.mp (hLQ hl) q).mp hq
  have hk : ⁅l,a⁆ ∈ centralizer (Q : Set G) := hLA (commutator_mem_commutator hl ha)
  have hcomm : ⁅a,l*q*l⁻¹⁆ ∈ Q :=
    le_normalizer_iff_commutator_le_right.mp hAQ (commutator_mem_commutator ha hq')
  have hzero : ⁅⁅l,a⁆,l*q*l⁻¹⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (hk _ hq').symm
  rw [conjugate_commutatorElement,show l*a*l⁻¹ = ⁅l,a⁆*a by
    simp [commutatorElement_def,mul_assoc],commutatorElement_mul_left_eq_conj_mul,
    hzero,mul_one,←hk _ hcomm,mul_inv_cancel_right]
  exact commutator_mem_commutator ha hq'

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

/-- The selected backward critical kernel is contained in the initial Baumann subgroup. -/
theorem CoordinatedChoice.critical_kernel_le_B
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (q : CriticalPath R s.geometry c.alpha1 (p.walk.getVert (p.walk.length-2)))
    (hq : q.walk.getVert 1=c.beta1) :
    Z R c.alpha1⊓Q R (p.walk.getVert (p.walk.length-2))≤
      B R (alpha R) (s.geometry.Z_normal _) := by
  let A := Z R c.alpha1⊓Q R (p.walk.getVert (p.walk.length-2))
  let K := Z R e⊓Q R (alpha R)
  have hAV : A≤V R (alpha R) := inf_le_left.trans c.back_layer_le_radius
  have hAn : Q R c.beta1≤normalizer (A:Set (FreeAmalgam R)) := by
    simpa only [hq] using s.critical_start_kernel_normalized_by_first_edge u hfull q
  have hK : K≤Q R c.beta1 := inf_le_right.trans
    (Q_le_adjacent_h R c.edge_color c.adjacent_start)
  have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
      (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull.le
  have hmove : ⁅A,Z R e⁆≤Z R (alpha R) := by
    by_cases hlarge : 4≤(Q R e).relIndex (Z R (alpha R))
    · exact (commutator_mono (le_inf hAV inf_le_right) le_rfl).trans
        (s.critical_radius_commutator_le_Z_of_two_lt h u hpnt hb p hlarge)
    have hsmall : (Q R e).relIndex (Z R (alpha R))<4 := by omega
    have hedge := s.critical_last_edge_inputs hb p
    have hfixed := s.small_edge_fixed_at h u (by
      simpa only [Model.pointCore_eq_exceptional] using hfull) p.end_color hedge.1
      (Z R (alpha R)) hedge.2.2 p.critical.2 (s.small_critical_fixedIndex_le_two h p hsmall)
    have hR : ⁅A,K⁆≤⁅Z R (alpha R),Z R e⁆ := by
      rw [commutator_comm]
      have hAt : A≤Q R (p.walk.getVert (p.walk.length-1)) := inf_le_right.trans hedge.2.1
      have hh := (commutator_mono le_rfl hAt).trans hfixed.1
      rw [←s.critical_kernel_eq_fixed p] at hh
      exact hh.trans (by rw [commutator_comm]; exact commutator_mono le_rfl (DistanceEight.U_le_Z R e))
    have hRZa : ⁅Z R (alpha R),Z R e⁆≤Z R (alpha R) :=
      ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R _)
    let := finite_Z R (alpha R)
    let : Finite (⁅Z R (alpha R),Z R e⁆:Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion hRZa) (inclusion_injective _)
    let : Finite (⁅A,K⁆:Subgroup (FreeAmalgam R)) :=
      Finite.of_injective (inclusion hR) (inclusion_injective _)
    have hcard : Nat.card (⁅A,K⁆:Subgroup (FreeAmalgam R))≤2 :=
      (card_le_of_le hR).trans_eq (s.small_critical_commutator_card h p hsmall)
    have hRn : Q R c.beta1≤normalizer ((⁅A,K⁆:Subgroup (FreeAmalgam R)):Set (FreeAmalgam R)) := by
      rw [commutator_comm]
      apply fixed_mod_central_normalizes_commutator K A (Q R c.beta1)
        (hK.trans hAn) hAn
      exact ((commutator_mono le_rfl hK).trans
        (s.edge_derived_le_kernel u hfull c.back_color c.adjacent_back)).trans
        ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q R c.alpha1 c.back_color))).trans (centralizer_le inf_le_left))
    have hRC : ⁅A,K⁆≤centralizer (Q R c.beta1:Set (FreeAmalgam R)) := by
      by_cases hc : Nat.card (⁅A,K⁆:Subgroup (FreeAmalgam R))=2
      · exact le_centralizer_iff.mp (hRn.trans (normalizer_le_centralizer_of_card_two _ hc))
      · rw [eq_bot_of_card_le (⁅A,K⁆:Subgroup (FreeAmalgam R)) (by omega)]
        exact bot_le
    have hRU : ⁅A,K⁆≤U R (alpha R) := hR.trans ((s.critical_Z_commutator_le_moving p).trans inf_le_left)
    have hRZe : ⁅A,K⁆≤Z R e := hR.trans
      (((s.critical_Z_commutator_le_moving p).trans inf_le_right).trans (DistanceEight.U_le_Z R _))
    have hRG : ⁅A,K⁆≤centralizer (stabilizer R (alpha R):Set (FreeAmalgam R)) := by
      apply le_centralizer_iff.mp
      rw [←c.generation,s.selectedCriticalLayer_eq h u hfull p]
      refine sup_le (le_centralizer_iff.mp hRC) ?_
      let := s.geometry.Z_elementary s.criticalDistance_pos e p.end_color
      exact le_centralizer_iff.mp (hRZe.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance))
    have hz : ⁅A,K⁆=⊥ := le_bot_iff.mp ((le_inf hRU
      (hRG.trans (centralizer_le (Ltilde_le_stabilizer _)))).trans_eq
        (s.movingLayer_inf_component_centralizer_eq_bot h))
    exact s.critical_commutator_le_start_of_predecessor_fixed h u hfull hb p A hAV
      (inf_le_right.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R _ q.end_color)))) (commutator_eq_bot_iff_le_centralizer.mp hz)
  apply c.critical_kernel_le_B_of_selected_normalizer s h u hfull hb q hq
  apply le_normalizer_iff_commutator_le_left.mpr
  apply le_trans _ le_sup_right
  apply commutator_sup_le_of_relative_normal (stabilizer R (alpha R)) A (Z R (alpha R))
    (Z R e) (Z R (alpha R)) (Z_normalized R (alpha R))
    (hAV.trans (s.geometry.V_local (alpha R) rfl hb)) (Z_le_stabilizer R _) hmove
  exact ((s.critical_Z_commutator_le_moving p).trans inf_le_left).trans (DistanceEight.U_le_Z R _)

/-- A small selected backward image gives the upper Baumann index in source (5.12)(3). -/
theorem CoordinatedChoice.small_backward_moving_index_le_two
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    {p : CriticalPath R s.geometry (alpha R) e} {delta : Vertex R}
    (c : s.CoordinatedChoice p delta)
    (q : CriticalPath R s.geometry c.alpha1 (p.walk.getVert (p.walk.length-2)))
    (hq : q.walk.getVert 1=c.beta1)
    (hsmall : (Q R (p.walk.getVert (p.walk.length-2))).relIndex (Z R c.alpha1)<4) :
    (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta)≤2 := by
  by_contra hn
  have hi : 2<(B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R delta) := by omega
  have hF : Z R c.alpha1⊓centralizer (Z R (p.walk.getVert (p.walk.length-2)):Set (FreeAmalgam R))≤
      Z R c.alpha1⊓Q R (p.walk.getVert (p.walk.length-2)) := by
    rintro z ⟨hz,hzc⟩
    refine ⟨hz,?_⟩
    rw [←s.C_eq_Q _ q.end_color]
    exact ⟨Z_le_stabilizer_of_dist_le c.alpha1 _ q.critical.1.le hz,hzc⟩
  exact s.small_backward_contradiction_of_commutator_line h u hfull hb c hi
    (Z R (p.walk.getVert (p.walk.length-2)))
    (critical_Z_le_stabilizer R s.geometry c.alpha1 c.back_color
      (by rw [s.geometry.distance_constant c.alpha1 c.back_color]; exact s.criticalDistance_pos) q.critical)
    (s.small_critical_commutator_card h q hsmall).le
    (hF.trans (c.critical_kernel_le_B s h u hfull hb q hq))

/-- The prescribed forward layer has index exactly two whenever the native
selected backward image is small. -/
theorem forward_moving_index_eq_two_of_small_choice
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2<s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (c : s.CoordinatedChoice p (p.walk.getVert 2))
    (hsmall : (Q R (p.walk.getVert (p.walk.length-2))).relIndex (Z R c.alpha1)<4) :
    (B R (alpha R) (s.geometry.Z_normal _)).relIndex (U R (p.walk.getVert 2))=2 := by
  have hi := s.forward_moving_index_two_le h u hfull hb p
  have hc := c.backward_critical_of_eligible s h u hfull hb (by omega)
  let w : (cosetGraph R).Walk c.alpha1 (alpha R) :=
    .cons ((cosetGraph_adj R _ _).mpr c.adjacent_back)
      (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R c.adjacent_start)) .nil)
  have hw : w.length=2 := rfl
  let q := p.prepend_two (by omega) c.back_color w hw hc.2
  have hq : q.walk.getVert 1=c.beta1 := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  exact Nat.le_antisymm (c.small_backward_moving_index_le_two s h u hfull hb q hq hsmall) hi
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The characteristic replacement gives the selected forward index in
source (5.12)(3), retaining only the alternating-block alternative. -/
theorem reducedSource_block_or_forward_index_two_of_small_choice
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (c : ((originalSource d hm).reduce r).CoordinatedChoice p (p.walk.getVert 2))
    (hb : 2<((originalSource d hm).reduce r).geometry.b r.radical)
    (hsmall : (Q r.radical (p.walk.getVert (p.walk.length-2))).relIndex
      (Z r.radical c.alpha1)<4) :
    IsAlternatingBlock L 6 ∨
      (B r.radical (alpha r.radical) (((originalSource d hm).reduce r).geometry.Z_normal _)).relIndex
        (U r.radical (p.walk.getVert 2))=2 := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    exact s.forward_moving_index_eq_two_of_small_choice (reduced_nativeCentralLayer d hm r)
      _ hf hb p c hsmall
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
