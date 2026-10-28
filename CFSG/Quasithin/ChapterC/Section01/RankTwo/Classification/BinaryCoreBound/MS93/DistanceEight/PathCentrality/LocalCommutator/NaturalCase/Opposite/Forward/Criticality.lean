module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Criticality of every avoiding forward continuation

If [Z_d,Z_a] lies in Z_b, then Z_a normalizes Z_d joined with Z_b and
therefore its Q_b-displacement, the actual order-four edge plane E_d.
Trivial action on U_b/E_d and the fixed summand of Z_b force the original
critical line into E_d, contradicting avoidance. In the noncritical case,
critical minimality puts Z_d inside Q_c. The original critical line and
[Z_a,Z_d] then generate the order-four selected edge. Both lie in V_b,
contradicting the source escape theorem through the selected centralizer bound.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite

private theorem normalizes_join_of_commutator_le {G : Type*} [Group G]
    (A B C : Subgroup G) (hBC : B ≤ normalizer C) (hcomm : ⁅A,B⁆ ≤ C) :
    B ≤ normalizer (A ⊔ C : Subgroup G) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hm : (A ⊔ C).map (MulAut.conj b).toMonoidHom ≤ A ⊔ C := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨a, ha, rfl⟩
      have hc : ⁅b,a⁆ ∈ C := by
        rw [commutator_comm] at hcomm
        exact hcomm (commutator_mem_commutator hb ha)
      have hh := (A ⊔ C).mul_mem (mem_sup_right hc) (mem_sup_left ha)
      simpa only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom,
        commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · exact (mem_normalizer_iff_map_conj_eq.mp (hBC hb)).le.trans le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj b).toMonoidHom hx)

private theorem small_join_eq {G : Type*} [Group G]
    (D T K : Subgroup G) [Finite K] (hDK : D ≤ K) (hTK : T ≤ K)
    (hD : Nat.card D = 2) (hK : Nat.card K ≤ 4) (hne : ¬ T ≤ D) :
    D ⊔ T = K := by
  have hJK : D ⊔ T ≤ K := sup_le hDK hTK
  let : Finite (D ⊔ T : Subgroup G) :=
    Finite.of_injective (inclusion hJK) (inclusion_injective _)
  have hlt : 2 < Nat.card (D ⊔ T : Subgroup G) := by
    by_contra! hh
    have he : D = D ⊔ T := eq_of_le_of_card_ge le_sup_left (by omega)
    exact hne (he ▸ le_sup_right)
  have hdvd : 2 ∣ Nat.card (D ⊔ T : Subgroup G) := hD ▸ card_dvd_of_le le_sup_left
  apply eq_of_le_of_card_ge hJK
  omega

namespace SelectedPath.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable {s : SelectedPath R geometry a c} (w : s.Continuation)

/-- The first noncontainment in the forward-continuation paragraph. -/
theorem commutator_not_le_endpoint_Z (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : ¬ ⁅Z R w.vertex, Z R s.start⁆ ≤ Z R s.endpoint := by
  intro h
  let E := edgeCommutator R s.endpoint w.intermediate
  have haG : Z R s.start ≤ stabilizer R s.endpoint :=
    (s.path.reverse common).endpoint_Z_le_start_stabilizer (by omega)
  have hbG : Z R s.endpoint ≤ stabilizer R s.start :=
    s.path.endpoint_Z_le_start_stabilizer (by omega)
  have hdG : Z R w.vertex ≤ stabilizer R s.endpoint :=
    geometry.Z_le_stabilizer_of_dist_le_b w.vertex w.vertex_color s.endpoint
      (by rw [w.endpoint_distance (by omega)]; omega)
  have heq : ⁅Z R w.vertex ⊔ Z R s.endpoint, Q R s.endpoint⁆ = E := by
    have hh := commutator_eq_of_centralizing_sup
      (show Z R s.endpoint ⊔ Z R w.vertex = Z R w.vertex ⊔ Z R s.endpoint from sup_comm _ _)
      (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes s.endpoint s.path.end_color))
      (hdG.trans (Q_normalized R s.endpoint))
    rw [commutator_comm (Q R s.endpoint) (Z R w.vertex),
      commutator_comm (Q R s.endpoint) (Z R w.vertex ⊔ Z R s.endpoint),
      w.displacement_eq_edge (by omega)] at hh
    exact hh.symm
  have hnJ : Z R s.start ≤ normalizer (Z R w.vertex ⊔ Z R s.endpoint : Subgroup (FreeAmalgam R)) :=
    normalizes_join_of_commutator_le _ _ _ (haG.trans (Z_normalized R s.endpoint)) h
  have hnE : Z R s.start ≤ normalizer (E : Set (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, ← heq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnJ hg),
      mem_normalizer_iff_map_conj_eq.mp ((haG.trans (Q_normalized R s.endpoint)) hg)]
  have hEU : E ≤ U R s.endpoint := Escape.EdgeTransfer.edge_commutator_le_natural
    common.large_distance (moduleFacts common) s.endpoint w.intermediate
    s.path.end_color w.adjacent_endpoint
  have hi : E.relIndex (U R s.endpoint) = 2 := by
    have hprod := (E.subgroupOf (U R s.endpoint)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hEU).toEquiv,
      w.edge_card common hb, common.natural.card_at s.endpoint s.path.end_color] at hprod
    change E.relIndex (U R s.endpoint) * 4 = 8 at hprod
    omega
  have hcomm : ⁅U R s.endpoint, Z R s.start⁆ ≤ E :=
    commutator_le_of_normalized_index_two _ _ _ hEU hi
      (haG.trans (U_normalized s.endpoint)) hnE
  have hfull : ⁅Z R s.start, Z R s.endpoint⁆ = ⁅Z R s.start, U R s.endpoint⁆ := by
    apply (commutator_eq_of_centralizing_sup
      (C := Z R s.endpoint ⊓ centralizer (stabilizer R s.endpoint : Set (FreeAmalgam R)))
      ?_ ?_ ?_).symm
    · exact (sup_comm _ _).trans ((naturalStructure common).decomposition_at
        s.endpoint s.path.end_color).symm
    · exact inf_le_right.trans (centralizer_le haG)
    · exact (U_le_Z R s.endpoint).trans (hbG.trans (Z_normalized R s.start))
  apply w.avoidance
  change ⁅Z R s.start, Z R s.endpoint⁆ ≤ E
  rw [hfull, commutator_comm]
  exact hcomm

/-- Every avoiding continuation is critical: the noncritical case forces the
selected edge into the endpoint radius group, contradicting escape. -/
theorem critical (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    CriticalPair R s.center w.vertex (geometry.exists_critical s.center (s.center_color (by omega))) := by
  by_contra hn
  have hdQ : Z R w.vertex ≤ Q R s.center := by
    by_contra h
    have hd := criticalDistance_le R w.vertex
      (geometry.exists_critical w.vertex w.vertex_color) h
    rw [geometry.distance_constant w.vertex w.vertex_color] at hd
    change geometry.b R ≤ (cosetGraph R).dist w.vertex s.center at hd
    have hdist : (cosetGraph R).dist w.vertex s.center = geometry.b R := by
      have hle := w.center_distance_le (by omega)
      rw [SimpleGraph.dist_comm] at hle
      omega
    apply hn
    exact common.critical_reverse w.vertex w.vertex_color s.center (s.center_color (by omega))
      ⟨hdist.trans (geometry.distance_constant w.vertex w.vertex_color).symm, h⟩
  have hbQ : Z R s.endpoint ≤ Q R s.center := by
    apply Z_le_Q_of_dist_lt R s.endpoint (geometry.exists_critical s.endpoint s.path.end_color)
    rw [geometry.distance_constant s.endpoint s.path.end_color, SimpleGraph.dist_comm,
      s.path.dist_end, s.path.length_eq_b]
    change geometry.b R - 2 < geometry.b R
    omega
  have hDE : s.criticalLine ≤ s.edge := by
    rw [← s.displacement_eq_edge (by omega)]
    exact commutator_mono le_rfl hbQ
  have hTE : ⁅Z R s.start, Z R w.vertex⁆ ≤ s.edge := by
    rw [← s.displacement_eq_edge (by omega)]
    exact commutator_mono le_rfl hdQ
  have haG : Z R s.start ≤ stabilizer R s.endpoint :=
    (s.path.reverse common).endpoint_Z_le_start_stabilizer (by omega)
  have hDZ : s.criticalLine ≤ Z R s.endpoint :=
    le_normalizer_iff_commutator_le_right.mp (haG.trans (Z_normalized R s.endpoint))
  let : Finite s.edge := Nat.finite_of_card_ne_zero (by rw [s.edge_card common hb]; decide)
  have he : s.criticalLine ⊔ ⁅Z R s.start, Z R w.vertex⁆ = s.edge :=
    small_join_eq _ _ _ hDE hTE (CriticalCase.critical_commutator_card common s.path)
      (s.edge_card common hb).le (by
        intro ht
        apply w.commutator_not_le_endpoint_Z common hb
        rw [commutator_comm]
        exact ht.trans hDZ)
  apply s.edge_not_le_endpoint_radius common hb
  rw [← he]
  have hnormal := le_normalizer_iff_commutator_le_right.mp
    (haG.trans (V_normalized R s.endpoint))
  exact sup_le
    ((commutator_mono le_rfl (Z_le_VBall R s.endpoint 2)).trans hnormal)
    ((commutator_mono le_rfl ((Z_le_localZSpan R w.vertex s.endpoint).trans
      (w.span_le_radius (by omega)))).trans hnormal)

end SelectedPath.Continuation
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
