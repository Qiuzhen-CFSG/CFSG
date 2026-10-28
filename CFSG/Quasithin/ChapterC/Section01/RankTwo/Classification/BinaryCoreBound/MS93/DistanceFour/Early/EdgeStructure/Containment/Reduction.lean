module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# The escaping-neighbor reduction for MS93 (4.6.4)

An edge displacement has order at most four: it is a proper commutator
subgroup of the natural group of order eight inside the finite edge two-group.
If a neighbor's displacement escapes B_alpha, the smaller commutator with
Q_alpha is central in V_alpha and has order two. Its nontriviality follows
from equality of the local kernel orders and X_alpha = Z_alpha.

The reduction also locates a genuine critical pair through alpha on which
the escaping displacement acts nontrivially. These are the opening local
steps of the contradiction on printed p.902. Neither the transfer (4.2)(i)
nor the final orbit-group contradiction is asserted here.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.4), printed p.902.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

private theorem finite_kernel (a : Vertex R) : Finite (Q R a) := by
  let := finite_stabilizer R a
  exact Finite.of_injective (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)

private theorem edge_kernel_two (source : LocalSource L R) (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) : IsPGroup 2 (Q R b) := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a b).mp hab
  · have hh := Q_act R g (beta R)
    simp only [beta, act_hVertex, one_mul] at hh
    rw [hh]
    change IsPGroup 2 ((neighborhoodKernel R (hVertex R 1)).map _)
    rw [neighborhoodKernel_h_base_eq_Sbar]
    exact (source.two_group.of_surjective (embedS R).rangeRestrict
      (embedS R).rangeRestrict_surjective).map _
  · change true = false at ha
    cases ha

private theorem proper_commutator {G : Type*} [Group G]
    (P A : Subgroup G) [Finite P] (hp : IsPGroup 2 P)
    (hAP : A ≤ P) (hne : A ≠ ⊥) : ⁅A, P⁆ ≠ A := by
  intro heq
  let A₀ := A.subgroupOf P
  have hcomm : ⁅A₀, (⊤ : Subgroup P)⁆ = A₀ := by
    apply map_injective P.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hAP, ← MonoidHom.range_eq_map, range_subtype, heq]
  have hz : A₀ ≤ ⊥ := le_normal_of_quotient_isPGroup_of_eq_commutator
    A₀ ⊤ ⊥ (hp.to_quotient ⊥) hcomm
  have hh := congrArg (Subgroup.map P.subtype) (le_bot_iff.mp hz)
  rw [map_subgroupOf_eq_of_le hAP, Subgroup.map_bot] at hh
  exact hne hh

include common in
/-- The binary edge displacement has order at most four, without assuming
that it is fixed by the edge kernel. -/
theorem edge_displacement_card_le_four (a b : Vertex R)
    (ha : color R a = false) (hab : Adjacent R a b) :
    Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  let := finite_kernel (R := R) b
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at a ha]; decide)
  have hU := edge_commutator_le_natural common a b ha hab
  let : Finite (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hU) (inclusion_injective hU)
  have hne : ⁅Z R a, Q R b⁆ ≠ U R a := by
    rw [edge_commutator_eq_natural common a b ha hab]
    apply proper_commutator (Q R b) (U R a) (edge_kernel_two source a b ha hab)
      ((U_le_Z a).trans (edge_Z_le_Q common a b ha hab))
    intro h
    have hh := common.natural.card_at a ha
    rw [h] at hh
    simp at hh
  have hdvd := card_dvd_of_le hU
  rw [common.natural.card_at a ha] at hdvd
  have hlt : Nat.card (⁅Z R a, Q R b⁆ : Subgroup (FreeAmalgam R)) < 8 := by
    by_contra! hh
    apply hne
    exact eq_of_le_of_card_ge hU (by rwa [common.natural.card_at a ha])
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

omit [Finite M] in
private theorem neighbor_color (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) : color R d = false := by
  have h₁ := adjacent_color_ne R hab
  have h₂ := adjacent_color_ne R hdb
  cases hb : color R b <;> cases hd : color R d <;> simp_all

omit [Finite M] in
private theorem neighbor_distance_le (a b d : Vertex R)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) : (cosetGraph R).dist d a ≤ 2 := by
  have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb)
  have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr (adjacent_symm R hab))
  have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := b) (w := a)
  omega

include common in
/-- A bad neighbor is a genuine vertex at distance two, and its displacement
is not central in the radius group. -/
theorem escaping_neighbor_geometry (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    color R d = false ∧ (cosetGraph R).dist d a = 2 ∧
      ¬ ⁅Z R d, Q R b⁆ ≤ (center (V R a)).map (V R a).subtype := by
  have hd := neighbor_color a b d ha hab hdb
  have hda := neighbor_distance_le a b d hab hdb
  have hne : d ≠ a := by
    intro h
    subst d
    exact hbad ((edge_commutator_le_natural common a b ha hab).trans
      ((U_le_Z a).trans (Z_le_B common a ha)))
  have hnonzero : (cosetGraph R).dist d a ≠ 0 := by
    intro h
    exact hne ((cosetGraph_connected R).dist_eq_zero_iff.mp h)
  have hnotone : (cosetGraph R).dist d a ≠ 1 := by
    intro h
    exact (adjacent_color_ne R ((cosetGraph_adj R _ _).mp
      (SimpleGraph.dist_eq_one_iff_adj.mp h))) (hd.trans ha.symm)
  exact ⟨hd, by omega, fun h => hbad (h.trans (initial.center_le_B a ha))⟩

omit [Finite M] in
/-- The smaller displacement is central in V_alpha, as required in the
opening paragraph of (4.6.4). -/
theorem neighbor_commutator_le_center (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b) :
    ⁅Z R d, Q R a⁆ ≤ (center (V R a)).map (V R a).subtype := by
  have hZ : Z R d ≤ V R a := le_iSup_of_le d
    (le_iSup_of_le (neighbor_distance_le a b d hab hdb) le_rfl)
  exact (commutator_mono hZ le_rfl).trans (initial.commutator_central a ha)

include common in
/-- An escaping neighbor cannot have trivial displacement under Q_alpha:
otherwise the equal-order local kernels, and hence their X = Z layers, coincide. -/
theorem escaping_neighbor_commutator_ne_bot
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅Z R d, Q R a⁆ ≠ ⊥ := by
  intro hzero
  have hd := neighbor_color a b d ha hab hdb
  have hb : color R b = true := by
    have hne := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  have hQa : Q R a ≤ Q R d := by
    rw [← common.centralizer d b hd hdb]
    exact le_inf (Q_le_adjacent_h R hb hab)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero))
  let := finite_kernel (R := R) d
  have heq : Q R a = Q R d := eq_of_le_of_card_ge hQa
    (by rw [source.Q_card a ha, source.Q_card d hd])
  have hZ : Z R d = Z R a := by
    rw [← common.X_eq_Z d hd, ← common.X_eq_Z a ha, X, X, heq]
  apply hbad
  rw [hZ]
  exact (edge_commutator_le_natural common a b ha hab).trans
    ((U_le_Z a).trans (Z_le_B common a ha))

include common in
/-- The strict containment between the two displacements forces the source
order q = 2 for [Z_delta,Q_alpha]. -/
theorem escaping_neighbor_commutator_card (initial : InitialFacts R geometry)
    (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    Nat.card (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  have hd := neighbor_color a b d ha hab hdb
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  have hAB : ⁅Z R d, Q R a⁆ ≤ ⁅Z R d, Q R b⁆ :=
    commutator_mono le_rfl (Q_le_adjacent_h R hb hab)
  have hBU := edge_commutator_le_natural common d b hd hdb
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at d hd]; decide)
  let : Finite (⁅Z R d, Q R b⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hBU) (inclusion_injective hBU)
  let : Finite (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hAB) (inclusion_injective hAB)
  have hlt : Nat.card (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) <
      Nat.card (⁅Z R d, Q R b⁆ : Subgroup (FreeAmalgam R)) := by
    by_contra! hn
    have heq := eq_of_le_of_card_ge hAB hn
    exact hbad (heq ▸ (neighbor_commutator_le_center initial a b d ha hab hdb).trans
      (initial.center_le_B a ha))
  have hlarge := (one_lt_card_iff_ne_bot _).mpr
    (escaping_neighbor_commutator_ne_bot common a b d ha hab hdb hbad)
  have hsmall := edge_displacement_card_le_four common d b hd hdb
  have hdvd := card_dvd_of_le (hAB.trans hBU)
  rw [common.natural.card_at d hd] at hdvd
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

omit [Finite M] in
private theorem Z_centralizes_own_kernel (geometry : Geometry R) (c : Vertex R) :
    ⁅Z R c, Q R c⁆ = ⊥ := by
  by_cases hc : color R c = false
  · exact geometry.centralizes c hc
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    rw [Z, if_neg hc]
    intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2

include common in
/-- Noncentrality of the escaping displacement supplies a critical pair
through alpha. The nested commutator retains the source order. -/
theorem escaping_neighbor_critical (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4)
    (a b d : Vertex R) (ha : color R a = false) (hd : color R d = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ∃ (c : Vertex R) (hc : color R c = false),
      (cosetGraph R).dist c a = 2 ∧ (cosetGraph R).dist b c = 3 ∧
      CriticalPair R d c (geometry.exists_critical d hd) ∧
      CriticalPair R c d (geometry.exists_critical c hc) ∧
      ⁅⁅Z R d, Q R b⁆, Z R c⁆ ≠ ⊥ := by
  classical
  have hgeometry := escaping_neighbor_geometry common initial a b d ha hab hdb hbad
  let D := ⁅Z R d, Q R b⁆
  have hDZ : D ≤ Z R d := (edge_commutator_le_natural common d b hd hdb).trans (U_le_Z d)
  have hDV : D ≤ V R a := hDZ.trans
    (le_iSup_of_le d (le_iSup_of_le hgeometry.2.1.le le_rfl))
  obtain ⟨c, hca, hnon⟩ : ∃ c, (cosetGraph R).dist c a ≤ 2 ∧ ⁅D, Z R c⁆ ≠ ⊥ := by
    by_contra! hn
    have hVD : V R a ≤ centralizer (D : Set (FreeAmalgam R)) := by
      apply iSup_le
      intro c
      apply iSup_le
      intro hc
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (hn c hc))
    have hDC := le_centralizer_iff.mpr hVD
    apply hgeometry.2.2
    intro x hx
    refine ⟨⟨x, hDV hx⟩, mem_center_iff.mpr ?_, rfl⟩
    intro y
    exact Subtype.ext (hDC hx y y.property)
  have hnot : ¬ Z R d ≤ Q R c := by
    intro h
    apply hnon
    apply le_bot_iff.mp
    exact (commutator_mono (hDZ.trans h) le_rfl).trans (by
      rw [commutator_comm, Z_centralizes_own_kernel geometry c])
  have hlo := criticalDistance_le R d (geometry.exists_critical d hd) hnot
  have hdist : (cosetGraph R).dist d c = 4 := by
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := c)
    rw [geometry.distance_constant d hd] at hlo
    change geometry.b R ≤ _ at hlo
    rw [hb] at hlo
    rw [SimpleGraph.dist_comm (u := a) (v := c)] at htri
    omega
  have hcrit : CriticalPair R d c (geometry.exists_critical d hd) :=
    ⟨by rw [geometry.distance_constant d hd]; exact hdist.trans hb.symm, hnot⟩
  have hc := critical_endpoint_color R d hd _ hcrit
  have hca2 : (cosetGraph R).dist c a = 2 := by
    have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := a) (w := c)
    rw [SimpleGraph.dist_comm (u := a) (v := c)] at htri
    omega
  have hbc : (cosetGraph R).dist b c = 3 := by
    have hlo := (cosetGraph_connected R).dist_triangle (u := d) (v := b) (w := c)
    have hhi := (cosetGraph_connected R).dist_triangle (u := b) (v := a) (w := c)
    have hdb1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb)
    have hba1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hab))
    rw [SimpleGraph.dist_comm (u := a) (v := c)] at hhi
    omega
  exact ⟨c, hc, hca2, hbc, hcrit, common.critical_reverse d hd c hc hcrit, hnon⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
