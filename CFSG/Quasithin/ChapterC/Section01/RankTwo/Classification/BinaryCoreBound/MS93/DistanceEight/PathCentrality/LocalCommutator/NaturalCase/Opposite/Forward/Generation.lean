module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Forward.Span
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Generation by the entire avoiding continuation orbit

The compatible marked local action realizes every natural plane as an incident
edge displacement. Edge transitivity fills every avoiding such edge by the
prescribed ordered-pair orbit. In an elementary group of order eight, each
point outside a line lies in a complementary plane: extend its disjoint cyclic
subgroup to a complement. Thus all points of the endpoint kernel plane outside
the original critical line lie in the generated continuation span. Multiplying
by one such point recovers the original line too.

Consequently endpointSpan equals U_b intersect Q_a and has order four.
The full-orbit bounds in Span now give the exact center displacement, including
its natural summand under the same marking, and the source radius bound.
The quotient image index and opposite moving-layer containment remain separate
proof obligations; no constructor for the full ForwardFacts is claimed here.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), printed p.891.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite

/-- In an elementary group of order eight, a line admits a complementary
plane through any specified point outside the line. -/
private theorem plane_through_outside {G : Type*} [Group G] [Finite G]
    [IsElementaryAbelian 2 G] (hG : Nat.card G = 8)
    (D : Subgroup G) (hD : Nat.card D = 2) {x : G} (hx : x ∉ D) :
    ∃ E : Subgroup G, Nat.card E = 4 ∧ x ∈ E ∧ ¬ D ≤ E := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx1 : x ≠ 1 := fun h => hx (h ▸ D.one_mem)
  have hx2 : x ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 G) x
  have hX : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx2 hx1
  have hd : Disjoint (zpowers x) D := by
    by_contra hn
    have hne : zpowers x ⊓ D ≠ ⊥ := fun hh => hn (disjoint_iff_inf_le.mpr hh.le)
    have hc := (one_lt_card_iff_ne_bot (zpowers x ⊓ D)).mpr hne
    have he : zpowers x ⊓ D = zpowers x := eq_of_le_of_card_ge inf_le_left (by omega)
    exact hx ((he.symm.le (mem_zpowers x)).2)
  let : ComplementedLattice (Subgroup G) := ⟨fun A => IsElementaryAbelian.exists_isCompl 2 G A⟩
  obtain ⟨E, hXE, hED⟩ := hd.exists_isCompl
  have hprod := card_sup_eq_mul_of_normalizes_of_disjoint E D le_normalizer_of_normal hED.disjoint
  rw [hED.sup_eq_top, card_top, hG, hD] at hprod
  refine ⟨E, by omega, hXE (mem_zpowers x), ?_⟩
  intro hDE
  have hbot : D = ⊥ := le_bot_iff.mp ((le_inf hDE le_rfl).trans hED.inf_eq_bot.le)
  rw [hbot, card_bot] at hD
  contradiction

namespace SelectedPath
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {source : LocalSource L R} {geometry : Geometry R} {a c : Vertex R}
variable (s : SelectedPath R geometry a c)

open Escape.Propagation.Backward.Products.Selection.Choices in
/-- Every avoiding natural plane is realized by an actual ordered-pair continuation. -/
theorem continuation_covers_plane (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) (E : Subgroup (FreeAmalgam R))
    (hEU : E ≤ U R s.endpoint) (hE : Nat.card E = 4) (havoid : ¬ s.criticalLine ≤ E) :
    ∃ w : s.Continuation, edgeCommutator R s.endpoint w.intermediate = E := by
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) s.endpoint s.path.end_color
  obtain ⟨w⟩ := s.continuation_exists common (by omega)
  have hU := Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (moduleFacts common) s.endpoint w.intermediate s.path.end_color w.adjacent_endpoint
  have hA : Nat.card (model.coordinates (edgeCommutator R s.endpoint w.intermediate)) = 4 :=
    (model.coordinates_card _ hU).trans (w.edge_card common hb)
  obtain ⟨u, hu⟩ := FiniteGeometry.plane_transitive _ hA
  obtain ⟨v, hv⟩ := FiniteGeometry.plane_transitive _ ((model.coordinates_card _ hEU).trans hE)
  obtain ⟨t, ht, he⟩ := model.realizes_plane source s.path.end_color w.adjacent_endpoint (v * u⁻¹)
  have htE : edgeCommutator R s.endpoint t = E := by
    apply model.coordinates_injective
      (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (moduleFacts common) s.endpoint t s.path.end_color ht) hEU
    change model.coordinates (Escape.edgeDisplacement s.endpoint t) = _
    rw [he]
    change FiniteGeometry.move (v * u⁻¹)
      (model.coordinates (edgeCommutator R s.endpoint w.intermediate)) = _
    rw [← hu, ← FiniteGeometry.move_mul, FiniteGeometry.move_cancel]
    exact hv
  obtain ⟨w', hw'⟩ := s.continuation_at (by omega) ht (htE ▸ havoid)
  exact ⟨w', by rw [hw', htE]⟩

/-- All points of the endpoint plane outside the original critical line
belong to the span of the avoiding continued commutators. -/
theorem outside_line_mem_endpointSpan (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {x : FreeAmalgam R}
    (hx : x ∈ U R s.endpoint ⊓ Q R s.start) (hxR : x ∉ s.criticalLine) :
    x ∈ s.endpointSpan := by
  let U₀ := U R s.endpoint
  let D := s.criticalLine.subgroupOf U₀
  have hDU : s.criticalLine ≤ U₀ := (s.criticalLine_le_endpoint_kernel common).trans inf_le_left
  have hU : Nat.card U₀ = 8 := common.natural.card_at _ s.path.end_color
  let : Finite U₀ := Nat.finite_of_card_ne_zero (by omega)
  let := geometry.U_elementary (by omega : 0 < geometry.b R) s.endpoint s.path.end_color
  have hD : Nat.card D = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDU).toEquiv).trans
      (CriticalCase.critical_commutator_card common s.path)
  obtain ⟨P, hP, hxP, hDP⟩ := plane_through_outside hU D hD (x := ⟨x,hx.1⟩) hxR
  let E := P.map U₀.subtype
  have hEU : E ≤ U₀ := map_subtype_le P
  have hE : Nat.card E = 4 := (card_map_of_injective U₀.subtype_injective).trans hP
  have havoid : ¬ s.criticalLine ≤ E := by
    intro h
    apply hDP
    intro d hd
    obtain ⟨p, hp, he⟩ := h hd
    have hpd : p = d := Subtype.ext he
    exact hpd ▸ hp
  obtain ⟨w, hw⟩ := s.continuation_covers_plane common hb E hEU hE havoid
  apply le_iSup (fun w : s.Continuation => s.endpointCommutator w) w
  rw [w.commutator_eq common hb, hw]
  exact ⟨mem_map_of_mem U₀.subtype hxP, hx.2⟩

/-- The entire avoiding ordered-pair orbit generates the actual endpoint plane. -/
theorem generated_eq (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    s.endpointSpan = U R s.endpoint ⊓ Q R s.start := by
  apply le_antisymm (s.endpointSpan_le_kernel common hb)
  have hnot : ¬ U R s.endpoint ⊓ Q R s.start ≤ s.criticalLine := by
    intro h
    have he := le_antisymm h (s.criticalLine_le_endpoint_kernel common)
    have hk := s.endpoint_kernel_card common hb
    rw [he, CriticalCase.critical_commutator_card common s.path] at hk
    contradiction
  obtain ⟨y, hy, hyR⟩ := SetLike.not_le_iff_exists.mp hnot
  have hyS := s.outside_line_mem_endpointSpan common hb hy hyR
  intro x hx
  by_cases hxR : x ∈ s.criticalLine
  · have hxyR : x * y ∉ s.criticalLine := by
      intro h
      exact hyR ((s.criticalLine.mul_mem_cancel_left hxR).mp h)
    have hxyS := s.outside_line_mem_endpointSpan common hb
      ((U R s.endpoint ⊓ Q R s.start).mul_mem hx hy) hxyR
    exact (s.endpointSpan.mul_mem_cancel_right hyS).mp hxyS
  · exact s.outside_line_mem_endpointSpan common hb hx hxR

/-- The order-four assertion for the actual generated avoiding span. -/
theorem generated_card (common : CommonFacts R source geometry) (hb : 4 < geometry.b R) :
    Nat.card s.endpointSpan = 4 := by
  rw [s.generated_eq common hb]
  exact s.endpoint_kernel_card common hb

namespace Continuation
variable {s} (w : s.Continuation)

/-- The full V0 displacement equals the plane generated by all avoiding continuations. -/
theorem center_commutator_eq (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    ⁅Z R s.center, s.continuationSpan w⁆ = s.endpointSpan :=
  w.center_commutator_eq_of_generated common hb (s.generated_eq common hb)

/-- The actual natural-module displacement has order four. -/
theorem center_commutator_card (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) : Nat.card (⁅Z R s.center, s.continuationSpan w⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  rw [w.center_commutator_eq common hb, s.generated_card common hb]

/-- The same order-four displacement is the displacement of the marked natural summand. -/
theorem natural_commutator_eq (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    ⁅U R s.center, s.continuationSpan w⁆ = s.endpointSpan := by
  have hspan : s.endpointSpan ≤ s.continuationSpan w :=
    (s.generated_eq common hb).le.trans (inf_le_left.trans ((U_le_Z R s.endpoint).trans
      (center_Z_le_span s.path.end_color (w.endpoint_distance (by omega)))))
  have hnorm : U R s.center ≤ normalizer (s.continuationSpan w : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono (U_le_Z R s.center) le_rfl).trans
        ((w.center_commutator_eq common hb).le.trans hspan))
  have hfixed : Z R s.center ⊓ centralizer (stabilizer R s.center : Set (FreeAmalgam R)) ≤
      centralizer (s.continuationSpan w : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le (w.span_le_center_stabilizer (by omega)))
  have he := commutator_eq_of_centralizing_sup
    ((sup_comm _ _).trans ((naturalStructure common).decomposition_at
      s.center (s.center_color (by omega))).symm) hfixed hnorm
  rw [commutator_comm (s.continuationSpan w) (U R s.center),
    commutator_comm (s.continuationSpan w) (Z R s.center)] at he
  exact he.trans (w.center_commutator_eq common hb)

/-- Cardinality for the displacement in the original natural marking at the center. -/
theorem natural_commutator_card (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    Nat.card (⁅U R s.center, s.continuationSpan w⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  rw [w.natural_commutator_eq common hb, s.generated_card common hb]

/-- The source radius bound with its generated-plane premise discharged. -/
theorem radius_commutator (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) :
    ⁅V R s.center ⊓ Q R s.endpoint, s.continuationSpan w⁆ ≤ s.endpointSpan :=
  w.radius_commutator_of_generated common hb (s.generated_eq common hb)

end Continuation
end SelectedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite
