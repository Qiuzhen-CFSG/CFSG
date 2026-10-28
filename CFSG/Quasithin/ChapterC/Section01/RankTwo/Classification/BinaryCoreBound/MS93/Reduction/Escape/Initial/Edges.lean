module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Paths
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# The binary edge upper bound before escape

The central fixed summand in Z makes no contribution to edge displacement.
The edge kernel is a finite two-group, so its commutator with the natural
eight-group is proper. This bounds every edge displacement by four.

Together with the geodesic containment, an order-four radius commutator
therefore equals the actual edge displacement. The argument uses LocalSource,
Geometry and ModuleFacts. It adapts the finite two-group calculation of
DistanceFour/Early/EdgeStructure/Containment/Reduction.lean to these earlier
inputs, without importing that later source branch.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(i), pp.882--883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

private theorem finite_kernel (a : Vertex R) : Finite (Q R a) := by
  let := finite_stabilizer R a
  exact Finite.of_injective (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)

private theorem edge_kernel_two (source : LocalSource L R) (a t : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) : IsPGroup 2 (Q R t) := by
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
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

theorem edge_eq_natural_commutator (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    edgeDisplacement a t = ⁅U R a, Q R t⁆ := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hQ : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hZa : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha,
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
    exact lt_trans (by decide : 1 < 2) hb
  have hh := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans (s.decomposition_at a ha).symm)
    (inf_le_right.trans (centralizer_le hQ))
    ((U_le_Z a).trans (hZa.trans (Q R t).le_normalizer))
  rw [edgeDisplacement, commutator_comm, ← hh, commutator_comm]

theorem edge_le_natural (source : LocalSource L R) (a t : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t) :
    edgeDisplacement a t ≤ U R a := by
  exact (commutator_mono le_rfl
    (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat))).trans
      (Z_commutator_stabilizer source a ha).le

theorem edge_card_le_four (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    Nat.card (edgeDisplacement a t) ≤ 4 := by
  let := finite_kernel (R := R) t
  let : Finite (U R a) := Nat.finite_of_card_ne_zero
    (by rw [modules.natural.card_at a ha]; decide)
  have hU := edge_le_natural source a t ha hat
  have hUt : U R a ≤ Q R t := by
    apply (U_le_Z a).trans
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha,
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)]
    exact lt_trans (by decide : 1 < 2) hb
  have hne : edgeDisplacement a t ≠ U R a := by
    rw [edge_eq_natural_commutator source hb modules a t ha hat]
    apply proper_commutator (Q R t) (U R a) (edge_kernel_two source a t ha hat) hUt
    intro h
    have hh := modules.natural.card_at a ha
    rw [h, card_bot] at hh
    omega
  have hdvd := card_dvd_of_le hU
  rw [modules.natural.card_at a ha] at hdvd
  have hlt : Nat.card (edgeDisplacement a t) < 8 := by
    by_contra! hh
    exact hne (eq_of_le_of_card_ge hU (by rwa [modules.natural.card_at a ha]))
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

theorem radius_eq_edge_of_card_four (p : Counterexample geometry) (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (hcard : Nat.card (radiusCommutator p.a p.a') = 4)
    (t : Vertex R) (ht : Before p.a p.a' t 1) :
    radiusCommutator p.a p.a' = edgeDisplacement p.a' t := by
  let := finite_stabilizer R p.a'
  let : Finite (edgeDisplacement p.a' t) := Finite.of_injective
    (inclusion ((edge_le_natural source p.a' t p.end_color ht.endpoint_adjacent).trans
      ((U_le_Z p.a').trans (Z_le_stabilizer R p.a')))) (inclusion_injective _)
  exact eq_of_le_of_card_ge (radius_le_edge p t ht)
    ((edge_card_le_four source hb modules p.a' t p.end_color ht.endpoint_adjacent).trans hcard.ge)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial
