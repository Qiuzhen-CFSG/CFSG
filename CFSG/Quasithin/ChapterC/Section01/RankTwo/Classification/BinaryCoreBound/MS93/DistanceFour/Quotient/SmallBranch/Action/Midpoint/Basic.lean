module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Descent
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.NormalizerTransfer

/-!
# Preliminary geometry of the actual midpoint actor

The midpoint kernel lies in the base stabilizer, so the radius subgroup has
an actual image under the given SL3(2) projection. Involution generation and
V_middle-prime = U_middle put every square in U_middle. The critical radius
puts U_middle inside Q_alpha, proving that this image is elementary abelian.
Its order is exactly the relative index of Q_alpha in V_middle.

The common edge kernel bounds both relevant relative indices by four. Critical
noncontainment rules out a trivial midpoint image, leaving order two or four.
The small-intersection hypothesis gives the printed fixed-preimage bound on
V_alpha/Z_alpha. A separate conditional lemma transports a commutator bound
modulo U_alpha to the required fixed-preimage index in the core.

Neither the exclusion of order two nor the passage from modulus Z_alpha to
U_alpha is proved here. In particular, this module does not construct
MidpointFacts, identify core intersect Z with U, or invoke natural coordinates.
All finiteness used for relative indices comes from finite vertex stabilizers.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.9)--(4.6.11), printed pp.908--909. The midpoint on p.909 is
alpha+2 and its displayed centralizer initially acts on V_alpha/Z_alpha.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common in
/-- The actual midpoint radius subgroup lies in the base M-factor. -/
theorem midpoint_locality (s : CriticalSegment geometry) : V R s.middle ≤ Mbar R := by
  have h := (Flags.V_le_Q geometry common.large_distance s.middle s.middle_color).trans
    (Q_le_stabilizer_of_dist_two R s.middle (alpha R) s.middle_color
      (by rw [SimpleGraph.dist_comm]; exact s.first_distance))
  simpa only [alpha, stabilizer_m_base] using h

omit [Finite M] in
include common in
/-- Critical-distance minimality places the midpoint natural layer in the base kernel. -/
theorem midpoint_U_le_Q (s : CriticalSegment geometry) : U R s.middle ≤ Q R (alpha R) := by
  apply (DistanceEight.U_le_Z R s.middle).trans
  apply Z_le_Q_of_dist_lt R s.middle (geometry.exists_critical s.middle s.middle_color)
  rw [geometry.distance_constant s.middle s.middle_color, SimpleGraph.dist_comm, s.first_distance]
  exact common.large_distance

omit [Finite M] in
include radius in
/-- Involution generation and the derived equality put radius squares in U. -/
theorem radius_square_mem_U (a : Vertex R) (ha : color R a = false)
    (x : V R a) : (x : FreeAmalgam R) ^ 2 ∈ U R a := by
  let P := V R a
  let f : P →* Abelianization P := (powMonoidHom 2).comp Abelianization.of
  have hle : P ≤ f.ker.map P.subtype := by
    change VBall R a 2 ≤ _
    conv_lhs => rw [← DistanceEight.VBall_omegaOne R a 2]
    apply (omegaOneAmbient_le_iff _ _).mpr
    intro y hy hy2
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    change (Abelianization.of (⟨y, hy⟩ : P)) ^ 2 = 1
    rw [← map_pow, show (⟨y, hy⟩ : P) ^ 2 = 1 from Subtype.ext hy2, map_one]
  obtain ⟨y, hy, he⟩ := hle x.property
  change (y : FreeAmalgam R) = x at he
  have hpow : y ^ 2 ∈ commutator P := by
    rw [← Abelianization.ker_of P]
    change Abelianization.of (y ^ 2) = 1
    rw [map_pow]
    exact hy
  have hh := mem_map_of_mem P.subtype hpow
  rw [← radius.radius_derived a ha]
  simpa only [_root_.commutator, map_commutator, ← MonoidHom.range_eq_map, range_subtype,
    subtype_apply, coe_pow, he] using hh

include common radius in
/-- The literal projected midpoint group is elementary abelian. -/
theorem midpointActor_elementary (s : CriticalSegment geometry) :
    IsElementaryAbelian 2 (midpointActor (source := source) s) := by
  have hp (x : midpointActor (source := source) s) : x ^ 2 = 1 := by
    obtain ⟨m, hm, he⟩ := x.property
    have hm2 : embedM R (m ^ 2) ∈ Q R (alpha R) := by
      rw [map_pow]
      exact midpoint_U_le_Q source geometry common s
        (radius_square_mem_U geometry radius s.middle s.middle_color ⟨embedM R m, hm⟩)
    rw [Q_alpha R source.two_group source.core_le] at hm2
    obtain ⟨n, hn, hnm⟩ := hm2
    have hn' : n = m ^ 2 := embedM_injective R hnm
    have hk : m ^ 2 ∈ source.projection.ker := by
      rw [source.projection_kernel, ← hn']
      exact hn
    apply Subtype.ext
    change (x : SL) ^ 2 = 1
    rw [← he, ← map_pow]
    exact hk
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun c => orderOf_dvd_of_pow_eq_one (hp c)) a b).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hp }

include common in
/-- The specified projection identifies actor order with the ambient relative index. -/
theorem midpointActor_card_eq_relIndex (s : CriticalSegment geometry) :
    Nat.card (midpointActor (source := source) s) = (Q R (alpha R)).relIndex (V R s.middle) := by
  rw [midpointActor, ← relIndex_ker, source.projection_kernel]
  rw [Q_alpha R source.two_group source.core_le]
  rw [← relIndex_map_map_of_injective _ _ (embedM_injective R)]
  rw [map_comap_eq]
  change (map (embedM R) (pCore 2 M)).relIndex (Mbar R ⊓ V R s.middle) = _
  rw [inf_eq_right.mpr (midpoint_locality source geometry common s)]

omit [Finite M] in
private theorem midpoint_common_neighbor (s : CriticalSegment geometry) :
    ∃ t, Adjacent R (alpha R) t ∧ Adjacent R s.middle t := by
  have hed : (cosetGraph R).edist (alpha R) s.middle = 2 := by
    rw [← ((cosetGraph_connected R) (alpha R) s.middle).coe_dist_eq_edist, s.first_distance]
    rfl
  obtain ⟨t, hat, hmt⟩ := (SimpleGraph.edist_eq_two_iff.mp hed).2.2
  exact ⟨t, (cosetGraph_adj R _ _).mp hat, (cosetGraph_adj R _ _).mp hmt⟩

include common radius in
/-- The common edge kernel bounds both midpoint indices by four. -/
theorem midpoint_indices_le_four (s : CriticalSegment geometry) :
    (Q R s.middle).relIndex (V R (alpha R)) ≤ 4 ∧
    (Q R (alpha R)).relIndex (V R s.middle) ≤ 4 := by
  obtain ⟨t, hat, hmt⟩ := midpoint_common_neighbor geometry s
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    have ha : color R (alpha R) = false := rfl
    cases h : color R t <;> simp_all
  have haQ : V R (alpha R) ≤ Q R t :=
    (Flags.V_le_Q geometry common.large_distance (alpha R) rfl).trans
      (Q_le_adjacent_h R ht hat)
  have hmQ : V R s.middle ≤ Q R t :=
    (Flags.V_le_Q geometry common.large_distance s.middle s.middle_color).trans
      (Q_le_adjacent_h R ht hmt)
  have hi := radius.edge_Q_index s.middle t s.middle_color hmt
  have hj := radius.edge_Q_index (alpha R) t rfl hat
  exact ⟨(relIndex_le_of_le_right haQ (by rw [hi]; decide)).trans hi.le,
    (relIndex_le_of_le_right hmQ (by rw [hj]; decide)).trans hj.le⟩

omit [Finite M] in
include common in
/-- The forward critical-path escape rules out containment of the base radius group. -/
theorem midpoint_radius_not_le (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    ¬ V R (alpha R) ≤ Q R s.middle := by
  apply common.escape (alpha R) rfl s.endpoint s.critical s.middle s.second_distance
  rw [s.first_distance, s.critical.1]
  exact hb.symm

include common in
/-- Reversal of the critical pair makes the midpoint image nontrivial. -/
theorem midpoint_not_le_base_kernel (s : CriticalSegment geometry) :
    ¬ V R s.middle ≤ Q R (alpha R) := by
  intro h
  have he := (common.critical_reverse (alpha R) rfl s.endpoint
    (critical_endpoint_color R (alpha R) rfl _ s.critical) s.critical).2
  apply he
  apply le_trans _ h
  exact le_iSup_of_le s.endpoint (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm]; exact s.second_distance.le) le_rfl)

include common radius in
/-- The proved geometric bounds leave only orders two and four. -/
theorem midpointActor_card_two_or_four (s : CriticalSegment geometry) :
    Nat.card (midpointActor (source := source) s) = 2 ∨
      Nat.card (midpointActor (source := source) s) = 4 := by
  let A := midpointActor (source := source) s
  let : IsElementaryAbelian 2 A := midpointActor_elementary source geometry common radius s
  have hle : Nat.card A ≤ 4 := by
    rw [show Nat.card A = (Q R (alpha R)).relIndex (V R s.middle) from
      midpointActor_card_eq_relIndex source geometry common s]
    exact (midpoint_indices_le_four source geometry common radius s).2
  have hne : Nat.card A ≠ 1 := by
    rw [show Nat.card A = (Q R (alpha R)).relIndex (V R s.middle) from
      midpointActor_card_eq_relIndex source geometry common s]
    intro h
    exact midpoint_not_le_base_kernel source geometry common s (relIndex_eq_one.mp h)
  have hpos : 0 < Nat.card A := Nat.card_pos
  rcases (IsElementaryAbelian.isPGroup 2 A).card_eq_or_dvd with h | h
  · exact False.elim (hne h)
  · change Nat.card A = 2 ∨ Nat.card A = 4
    omega

include common radius in
/-- The small-intersection hypothesis proves the printed bound modulo Z_alpha. -/
theorem midpoint_radius_fixed_index (s : CriticalSegment geometry) (hs : s.SmallIntersection) :
    (commutatorPreimage (V R (alpha R)) (V R s.middle) (Z R (alpha R))).relIndex
      (V R (alpha R)) ≤ 4 := by
  let P := V R (alpha R)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  have hP : P ≤ stabilizer R (alpha R) :=
    (Flags.V_le_Q geometry common.large_distance (alpha R) rfl).trans (fun _ hx => hx.1)
  let : Finite P := Finite.of_injective (inclusion hP) (inclusion_injective hP)
  have hle := le_commutatorPreimage (inf_le_left : P ⊓ Q R s.middle ≤ P) hs
  have hh := relIndex_le_of_le_left hle
    (show (P ⊓ Q R s.middle).relIndex P ≠ 0 from Subgroup.index_ne_zero_of_finite)
  rw [inf_relIndex_left] at hh
  exact hh.trans (midpoint_indices_le_four source geometry common radius s).1

include common radius in
/-- A commutator containment modulo U_alpha suffices for the actual core fixed index.
The containment is an explicit additional premise, not inferred from the small branch. -/
theorem midpoint_fixed_index_of_commutator (s : CriticalSegment geometry)
    (hcomm : ⁅core R (alpha R) ⊓ Q R s.middle, V R s.middle⁆ ≤ U R (alpha R)) :
    (commutatorPreimage (core R (alpha R)) (V R s.middle) (U R (alpha R))).relIndex
      (core R (alpha R)) ≤ 4 := by
  let C := core R (alpha R)
  let K := commutatorPreimage C (V R s.middle) (U R (alpha R))
  have hC : C ≤ stabilizer R (alpha R) := (core_le_Q source).trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite C := Finite.of_injective (inclusion hC) (inclusion_injective hC)
  have hV : V R (alpha R) ≤ stabilizer R (alpha R) :=
    (Flags.V_le_Q geometry common.large_distance (alpha R) rfl).trans (fun _ hx => hx.1)
  let : Finite (V R (alpha R)) := Finite.of_injective (inclusion hV) (inclusion_injective hV)
  have hsub : C ⊓ Q R s.middle ≤ K := le_commutatorPreimage inf_le_left hcomm
  have hindex : K.relIndex C ≤ (Q R s.middle).relIndex C := by
    have h := relIndex_le_of_le_left hsub (show (C ⊓ Q R s.middle).relIndex C ≠ 0 from
      Subgroup.index_ne_zero_of_finite)
    simpa only [inf_relIndex_left] using h
  exact hindex.trans ((relIndex_le_of_le_right (radius.core_le_radius (alpha R) rfl)
    (show (Q R s.middle).relIndex (V R (alpha R)) ≠ 0 from
      Subgroup.index_ne_zero_of_finite)).trans
        (midpoint_indices_le_four source geometry common radius s).1)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
