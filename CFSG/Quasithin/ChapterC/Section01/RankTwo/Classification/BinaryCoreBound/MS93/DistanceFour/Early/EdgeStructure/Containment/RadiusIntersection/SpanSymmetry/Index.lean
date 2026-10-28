module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.RadiusIndex

/-!
# The abelian-span symmetry index bound

The paired critical segment excludes a bad edge displacement at its midpoint:
such a displacement would have an abelian stabilizer span, hence that span
would lie in the midpoint kernel. Simultaneous conjugate escape, applied to
the seed joined with the initial Z-layer, gives the opposite conclusion.
This supplies the source's symmetry step with its bad-neighbor hypothesis
proved explicitly.

The original bad displacement has order four, because its kernel displacement
has order two and is strictly smaller. Edge conjugacy transports that order
to the midpoint. The local fixed summand of the midpoint Z-layer lies in the
initial Z-layer, so the order-four displacement in the order-eight natural
group bounds the literal B-intersection index by two.

This module proves the index bound. Centralization of that B-intersection
in the radius remains a separate step; no equality of B with the radius
center, universal edge containment, or later edge-order theorem is used.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (2.1)(vi--vii), (2.2)(iv), and (4.6.4), printed pp.855--857, 902.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)
include common in
private theorem escaping_span_not_le_midpoint_kernel (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (r e : Vertex R) (hr : color R r = false)
    (hcrit : CriticalPair R a r (geometry.exists_critical a ha))
    (hrb : Z R r ≤ Q R b) (hR : ⁅Z R r, Q R e⁆ ≤ Z R a) :
    ¬ neighborSpan a d ≤ Q R e := by
  have hd := (escaping_neighbor_geometry common initial a b d ha hab hdb hbad).1
  have hda := (escaping_neighbor_geometry common initial a b d ha hab hdb hbad).2.1
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases hc : color R b <;> simp_all
  have hQaQb := Q_le_adjacent_h R hcolb hab
  have hZda := (neighborSpan_le_radius a d hda.le).trans (radius_le_Q common a ha)
  have hZaa : Z R a ≤ Q R a := by rw [← common.X_eq_Z a ha]; exact omegaCenter_le _
  have hQbGa : Q R b ≤ stabilizer R a := by rw [Q_h_eq_edge R hcolb hab]; exact inf_le_left
  have hQbGd : Q R b ≤ stabilizer R d := by rw [Q_h_eq_edge R hcolb hdb]; exact inf_le_left
  have hSN : Q R b ≤ normalizer (Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
    (le_inf (hQbGd.trans (Z_normalized R d)) (hQbGa.trans (Z_normalized R a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSnonnormal : ¬ ((Z R d ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
    obtain ⟨c,hc,hca,_,hdc,_,_⟩ :=
      escaping_neighbor_critical common initial hb a b d ha hd hab hdb hbad
    have hh := (critical_nonnormal_forward R geometry common.centralizer d hd
      (by rw [geometry.distance_constant d hd]; exact lt_trans (by decide) common.large_distance)
      c hdc a hda (by
        rw [SimpleGraph.dist_comm (u := a), hca, hdc.1, geometry.distance_constant d hd]
        exact hb.symm)).2
    simpa only [common.X_eq_Z a ha] using hh
  have hgen := OrderTwo.edge_conjugate_generation source a b ha hab (Z R r) hrb
    (common.critical_reverse a ha r hr hcrit).2
  have hSQb : Z R d ⊔ Z R a ≤ Q R b :=
    (sup_le ((Z_le_neighborSpan a d).trans hZda) hZaa).trans hQaQb
  obtain ⟨g,hga,hn,_⟩ := source_2_1_vii R a r b ha hab
    (Z R d ⊔ Z R a) (Z R d ⊔ Z R a) hSQb hSQb
    (normal_subgroupOf_of_le_normalizer hSN) (normal_subgroupOf_of_le_normalizer hSN)
    hSnonnormal hSnonnormal hgen
  intro hle
  have hfix : act R g a = a := hga
  have hseed : Z R (act R g d) ≤ neighborSpan a d := by
    rw [Z_act]
    exact le_iSup_of_le (⟨g⁻¹,(stabilizer R a).inv_mem hga⟩ : stabilizer R a) le_rfl
  have hdist : (cosetGraph R).dist a (act R g d) = 2 := by
    rw [← hfix, dist_act, SimpleGraph.dist_comm]
    exact hda
  have hcomm : ⁅Z R (act R g d), Z R r⁆ ≤ Z R a :=
    (commutator_mono (hseed.trans hle) le_rfl).trans (by rwa [commutator_comm])
  apply hn
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hfix]
  exact (source_2_1_vi R source geometry a ha
    (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide) common.large_distance)
    hcrit (act R g d) hdist (hseed.trans hZda) (hcomm.trans le_sup_right)).1


include common in
/-- The opposite midpoint cannot itself have an escaping edge displacement. -/
theorem paired_edge_le_B
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    ⁅Z R p.e, Q R b⁆ ≤ B R a (geometry.Z_normal a) := by
  by_contra hbad
  have hc := escaping_neighborSpan_commutative common initial hb a b p.e ha hab p.edge hbad
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  apply escaping_span_not_le_midpoint_kernel common initial hb a b p.e ha hab p.edge hbad
    p.r p.e p.hr p.critical p.seed_edge (p.layer_right.trans inf_le_left)
  rw [← common.centralizer p.e b p.he p.edge]
  refine le_inf ((neighborSpan_le_radius a p.e (by rw [SimpleGraph.dist_comm]; exact p.near.le)).trans
    ((radius_le_Q common a ha).trans (Q_le_adjacent_h R hcolb hab))) ?_
  exact (le_centralizer_iff_isMulCommutative.mpr hc).trans
    (centralizer_le (Z_le_neighborSpan a p.e))


include common in
private theorem escaping_edge_card_four (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    Nat.card (⁅Z R d,Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  have hd := (escaping_neighbor_geometry common initial a b d ha hab hdb hbad).1
  have hcolb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  have hle : ⁅Z R d,Q R a⁆ ≤ ⁅Z R d,Q R b⁆ :=
    commutator_mono le_rfl (Q_le_adjacent_h R hcolb hab)
  have hDU := edge_commutator_le_natural common d b hd hdb
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at d hd]; decide)
  let : Finite (⁅Z R d,Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hDU) (inclusion_injective _)
  have hcard := escaping_neighbor_commutator_card common initial a b d ha hab hdb hbad
  have hlt : 2 < Nat.card (⁅Z R d,Q R b⁆ : Subgroup (FreeAmalgam R)) := by
    by_contra! hsmall
    have heq := eq_of_le_of_card_ge hle (by omega)
    exact hbad (heq ▸ (neighbor_commutator_le_center initial a b d ha hab hdb).trans
      (initial.center_le_B a ha))
  have hdiv : Nat.card (⁅Z R d,Q R b⁆ : Subgroup (FreeAmalgam R)) ∣ 8 := by
    simpa only [common.natural.card_at d hd] using card_dvd_of_le hDU
  have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1,2,4,8} : Finset ℕ) by decide] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  have hbound := edge_displacement_card_le_four common d b hd hdb
  omega

include common in
/-- The fixed summand at a distance-two vertex is already in the initial Z-layer. -/
theorem midpoint_fixed_le_Z (a e : Vertex R) (ha : color R a = false)
    (he : color R e = false) (hnear : (cosetGraph R).dist a e = 2) :
    Z R e ⊓ centralizer (stabilizer R e : Set (FreeAmalgam R)) ≤ Z R a := by
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) e he
  have hZeQ : Z R e ≤ Q R a := Z_le_Q_of_dist_lt R e (geometry.exists_critical e he) (by
    rw [SimpleGraph.dist_comm, hnear, geometry.distance_constant e he]
    exact common.large_distance)
  have hQaGe := Q_le_stabilizer_of_dist_two R a e ha hnear
  rw [← common.X_eq_Z a ha]
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZeQ hx.1,
    elemPow_eq_one_of_isElementaryAbelian x hx.1, centralizer_le hQaGe hx.2⟩

private theorem supplement_index {G : Type*} [Group G]
    (Z U C K : Subgroup G) [IsMulCommutative Z]
    (hsplit : Z = U ⊔ C) (hC : C ≤ K) : K.relIndex Z = K.relIndex U := by
  have hUZ : U ≤ Z := hsplit ▸ le_sup_left
  have hCZ : C ≤ Z := hsplit ▸ le_sup_right
  let K₀ := K.subgroupOf Z
  let U₀ := U.subgroupOf Z
  have hsup : U₀ ⊔ K₀ = ⊤ := by
    apply map_injective Z.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hUZ,
      subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype]
    apply le_antisymm (sup_le hUZ inf_le_right)
    calc
      Z = U ⊔ C := hsplit
      _ ≤ U ⊔ (K ⊓ Z) := sup_le le_sup_left
        ((show C ≤ K ⊓ Z from le_inf hC hCZ).trans le_sup_right)
  have hh := relIndex_sup_right U₀ K₀
  rw [hsup, relIndex_top_right, relIndex_subgroupOf hUZ] at hh
  exact hh

include common in
/-- The literal B-intersection at the paired midpoint has index at most two.
The order-four edge displacement is deduced from the original bad neighbor,
not from any later universal edge-order assertion. -/
theorem paired_span_index_le_two
    (initial : InitialFacts R geometry) (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    (B R a (geometry.Z_normal a)).relIndex (Z R p.e) ≤ 2 := by
  let naturalData : BinaryNaturalStructure source :=
    ⟨common.X_eq_Z, common.natural, common.decomposition, common.disjoint⟩
  let := geometry.Z_elementary (lt_trans (by decide : 0 < 2) common.large_distance) p.e p.he
  let : Finite (U R p.e) := Nat.finite_of_card_ne_zero (by
    rw [common.natural.card_at p.e p.he]; decide)
  have hD := paired_edge_le_B common initial hb a b d ha hab p
  have hDU := edge_commutator_le_natural common p.e b p.he p.edge
  have hd := (escaping_neighbor_geometry common initial a b d ha hab hdb hbad).1
  have hcard : Nat.card (⁅Z R p.e,Q R b⁆ : Subgroup (FreeAmalgam R)) = 4 :=
    (OrderTwo.edge_card_eq p.e b d b p.he hd p.edge hdb).trans
      (escaping_edge_card_four common initial a b d ha hab hdb hbad)
  have hindex : (⁅Z R p.e,Q R b⁆ : Subgroup (FreeAmalgam R)).relIndex (U R p.e) = 2 := by
    have hh := ((⁅Z R p.e,Q R b⁆ : Subgroup (FreeAmalgam R)).subgroupOf (U R p.e)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hDU).toEquiv, hcard,
      common.natural.card_at p.e p.he] at hh
    change 4 * (⁅Z R p.e,Q R b⁆ : Subgroup (FreeAmalgam R)).relIndex (U R p.e) = 8 at hh
    omega
  rw [supplement_index (Z R p.e) (U R p.e)
    (Z R p.e ⊓ centralizer (stabilizer R p.e : Set (FreeAmalgam R)))
    (B R a (geometry.Z_normal a)) (naturalData.decomposition_at p.e p.he)
    ((midpoint_fixed_le_Z common a p.e ha p.he p.near).trans (Z_le_B common a ha))]
  have hh := relIndex_le_of_le_left hD
    (show (⁅Z R p.e,Q R b⁆ : Subgroup (FreeAmalgam R)).relIndex (U R p.e) ≠ 0 from
      index_ne_zero_of_finite)
  exact hh.trans_eq hindex

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanSymmetry
