module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ForwardSpanAction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.SelectedKernel
/-!
# The opposite critical seed acts with fixed index at most two

Let P be the normal span of the second-vertex Z-layer at critical distance
four. For Y=P intersect Q_c the opposite commutator [Y,Z_e] lies in Z_alpha.
The large-image radius bound gives this directly. In the small-image case,
[Y,Z_e intersect Q_alpha] lies both in the initial moving layer and in the
forward line fixed by the starting stabilizer, so it vanishes. The
predecessor calculation then applies. Since Z_alpha centralizes P, the
literal descended action on P/Z(P) fixes the image of Y, of index at most
two. No faithfulness or module recognition is assumed in this calculation.

This supplies the endpoint-action input in the last paragraph of MS93
(5.12), printed p.927, with its actual Chapter13 source application.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

theorem forward_span_endpoint_kernel_commutator_le_Z
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ⁅localZSpan R (p.walk.getVert 2) (alpha R)⊓Q R (p.walk.getVert 2),Z R e⁆≤Z R (alpha R) := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let Y := P⊓Q R (p.walk.getVert 2)
  let K := Z R e⊓Q R (alpha R)
  let T₀ := Q R (alpha R)⊓centralizer
    (U R (p.walk.getVert 2)⊓B R (alpha R) (s.geometry.Z_normal _):Set (FreeAmalgam R))
  let H := ⁅U R (p.walk.getVert 2),T₀⁆
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hb2 : 2<s.geometry.b R := by omega
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color (by omega)).mpr (by decide)
  have hPV : P≤V R (alpha R) := localZSpan_le_V R (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hYV : Y≤V R (alpha R) := inf_le_left.trans hPV
  have hYQ : Y≤Q R (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using (inf_le_right : Y≤Q R (p.walk.getVert 2))
  by_cases hlarge : 4≤(Q R e).relIndex (Z R (alpha R))
  · have hpnt : R.map s.projection≤Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj u).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull.le
    exact (commutator_mono (le_inf hYV hYQ) le_rfl).trans
      (s.critical_radius_commutator_le_Z_of_two_lt h u hpnt hb2 p hlarge)
  have hsmall : (Q R e).relIndex (Z R (alpha R))<4 := by omega
  have hedge := s.critical_last_edge_inputs hb2 p
  have hfixed := s.small_edge_fixed_at h u (by
    simpa only [Model.pointCore_eq_exceptional] using hfull) p.end_color hedge.1
    (Z R (alpha R)) hedge.2.2 p.critical.2 (s.small_critical_fixedIndex_le_two h p hsmall)
  have hR : ⁅Y,K⁆≤⁅Z R (alpha R),Z R e⁆ := by
    rw [commutator_comm]
    have hYt := hYQ.trans hedge.2.1
    have hh := (commutator_mono le_rfl hYt).trans hfixed.1
    rw [←s.critical_kernel_eq_fixed p] at hh
    exact hh.trans (by rw [commutator_comm]; exact commutator_mono le_rfl (DistanceEight.U_le_Z R e))
  have hKT : K≤T₀ := le_sup_right.trans (s.critical_forward_kernel_contains_inner_layers_of_two_lt hb2 p)
  have hi := s.forward_moving_index_eq_two_of_distance_four h u hfull hb p
  have hspan := s.critical_forward_span_commutator_le_line_of_two_lt h u hfull hb2 p hi.le
  have hH : ⁅Y,K⁆≤H := (commutator_mono inf_le_left hKT).trans hspan.2
  have hU : ⁅Y,K⁆≤U R (alpha R) := hR.trans ((s.critical_Z_commutator_le_moving p).trans inf_le_left)
  have hC : ⁅Y,K⁆≤centralizer (Ltilde R (alpha R):Set (FreeAmalgam R)) :=
    (hH.trans hspan.1).trans (centralizer_le (Ltilde_le_stabilizer _))
  have hz : ⁅Y,K⁆=⊥ := le_bot_iff.mp ((le_inf hU hC).trans_eq
    (s.movingLayer_inf_component_centralizer_eq_bot h))
  apply s.critical_commutator_le_start_of_predecessor_fixed h u hfull hb2 p Y hYV
  · simpa only [hl,Nat.reduceSub] using (inf_le_right.trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R _ hc))) :
        Y≤centralizer (Z R (p.walk.getVert 2):Set (FreeAmalgam R)))
  · exact commutator_eq_bot_iff_le_centralizer.mp hz

theorem forward_span_endpoint_kernel_commutator_central
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    let P := localZSpan R (p.walk.getVert 2) (alpha R)
    ⁅P⊓Q R (p.walk.getVert 2),Z R e⁆≤(center P).map P.subtype := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  change ⁅P⊓Q R (p.walk.getVert 2),Z R e⁆≤(center P).map P.subtype
  have hb2 : 2<s.geometry.b R := by omega
  have hPQ : P≤Q R (alpha R) := (s.forward_span_le_hyperplane_kernel hb2 p).trans inf_le_left
  have hZaC : Z R (alpha R)≤centralizer (P:Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R _ rfl)).trans (centralizer_le hPQ)
  have hZeG : Z R e≤stabilizer R (alpha R) :=
    critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical
  have hCP : ⁅P⊓Q R (p.walk.getVert 2),Z R e⁆≤P :=
    (commutator_mono inf_le_left le_rfl).trans (le_normalizer_iff_commutator_le_left.mp
      (hZeG.trans (localZSpan_normalized R _ _)))
  have hc := (s.forward_span_endpoint_kernel_commutator_le_Z h u hfull hb p).trans hZaC
  intro z hz
  refine ⟨⟨z,hCP hz⟩,?_,rfl⟩
  exact mem_center_iff.mpr (fun w => Subtype.ext (hc hz w w.property))

theorem forward_span_endpoint_fixed_index
    (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection=Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : s.geometry.b R=4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (ρ : Model.S →* MulAut ((localZSpan R (p.walk.getVert 2) (alpha R)) ⧸
        center (localZSpan R (p.walk.getVert 2) (alpha R))))
    (hρ : ∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R (p.walk.getVert 2) m)
    (m : M) (hm : embedM R m∈Z R e) :
    (ρ (s.projection m)).fixedSubgroup.index≤2 := by
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  let C := Q R (p.walk.getVert 2)
  let q : P →* P⧸center P := QuotientGroup.mk' (center P)
  have hb2 : 2<s.geometry.b R := by omega
  have hPG : P≤stabilizer R (alpha R) :=
    ((s.forward_span_le_hyperplane_kernel hb2 p).trans inf_le_left).trans (by intro x hx; exact hx.1)
  let := finite_stabilizer R (alpha R)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  have hc := s.forward_span_endpoint_kernel_commutator_central h u hfull hb p
  change ⁅P⊓C,Z R e⁆≤(center P).map P.subtype at hc
  have hfix : (C.subgroupOf P).map q≤(ρ (s.projection m)).fixedSubgroup := by
    rintro _ ⟨x,hx,rfl⟩
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    rw [hρ,forwardSpanCentralAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change forwardSpanAction R (p.walk.getVert 2) m x / x ∈ center P
    have hz : ⁅embedM R m,(x:FreeAmalgam R)⁆∈(center P).map P.subtype := by
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator hm ⟨x.property,hx⟩
    obtain ⟨z,hz,hze⟩ := hz
    have he : forwardSpanAction R (p.walk.getVert 2) m x / x=z := by
      apply Subtype.ext
      change embedM R m*(x:FreeAmalgam R)*(embedM R m)⁻¹/(x:FreeAmalgam R)=(z:FreeAmalgam R)
      simpa only [div_eq_mul_inv,commutatorElement_def,Subgroup.subtype_apply] using hze.symm
    rw [he]
    exact hz
  have hi : ((C.subgroupOf P).map q).index≤C.relIndex P := Nat.le_of_dvd
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((C.subgroupOf P).index_map_dvd (QuotientGroup.mk'_surjective (center P)))
  exact (index_antitone hfix).trans (hi.trans (s.forward_span_second_vertex_index_le_two h u hfull hb p))
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)

@[expose] def ForwardSpanEndpointData {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) : Prop :=
  let P := localZSpan R (p.walk.getVert 2) (alpha R)
  ∀ (ρ : Model.S →* MulAut (P⧸center P)),
    (∀ m : M, ρ (s.projection m)=forwardSpanCentralAction R (p.walk.getVert 2) m) →
    ∀ m : M, embedM R m∈Z R e → (ρ (s.projection m)).fixedSubgroup.index≤2
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K] {L W : Subgroup K} [L.Normal] [W.Normal]
  {T : Sylow 2 K} (d : NaturalSixControl.SourceData L W T) (hm : IntrinsicMSPair d)
local notation "J" => (L⊔d.B:Subgroup K)

theorem reducedSource_block_or_forward_span_endpoint
    (r : CharacteristicReduction (L.subgroupOf J) (d.B.subgroupOf J)) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d hm).reduce r).geometry (alpha r.radical) e)
    (hb : ((originalSource d hm).reduce r).geometry.b r.radical=4) :
    IsAlternatingBlock L 6 ∨ ((originalSource d hm).reduce r).ForwardSpanEndpointData p := by
  rcases reducedSource_block_or_full_point_image d hm r with hblock|hfull
  · exact Or.inl hblock
  · right
    let s := (originalSource d hm).reduce r
    have hf : r.radical.map s.projection=Model.E.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hfull
    have h := reduced_nativeCentralLayer d hm r
    exact fun ρ hρ m hm => s.forward_span_endpoint_fixed_index h _ hf hb p ρ hρ m hm
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
