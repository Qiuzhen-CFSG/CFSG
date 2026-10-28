module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Requirements

/-!
# Midpoint geometry before the large-branch rank-one recognition

At distance two the intersection V_a ∩ Q_c is exactly C_{V_a}(Z_c).
The neighboring edge kernel bounds its relative index by four; the radius
commutator identity proves normality inside V_a. A critical midpoint has
index at least two, and the escape clause puts its Z-layer outside B_a.
Local transitivity also puts Z_alpha inside its actual full orbit span.

These are the geometric inputs to MS93 (1993), (4.6.12)(1)--(5), printed
pp.910--912. The exact natural rank-one quotient, the conjugate-span
recognition, and the starred index 64 are not asserted here.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

/-- A distance-two pair has a common adjacent vertex in the actual coset graph. -/
theorem distance_two_neighbor {a c : Vertex R}
    (hd : (cosetGraph R).dist a c = 2) :
    ∃ b, Adjacent R a b ∧ Adjacent R b c := by
  have he : (cosetGraph R).edist a c = 2 := by
    rw [← ((cosetGraph_connected R) a c).coe_dist_eq_edist, hd]
    rfl
  obtain ⟨b, hab, hcb⟩ := (SimpleGraph.edist_eq_two_iff.mp he).2.2
  exact ⟨b, (cosetGraph_adj R _ _).mp hab,
    adjacent_symm R ((cosetGraph_adj R _ _).mp hcb)⟩

/-- Both ends of a distance-two path have the same M-color. -/
theorem distance_two_color {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) : color R c = false := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a c
  have he : Even p.length := by rw [hp, hd]; decide
  exact ((walk_even_iff_color_eq R p).mp he).symm.trans ha

include common in
/-- The midpoint kernel cuts out the literal centralizer of its Z-layer. -/
theorem radius_inf_kernel [Finite M] {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) :
    V R a ⊓ Q R c = V R a ⊓ centralizer (Z R c : Set (FreeAmalgam R)) := by
  obtain ⟨b, hab, hbc⟩ := distance_two_neighbor hd
  have hc := distance_two_color ha hd
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  have hVQ : V R a ≤ Q R b :=
    (Flags.V_le_Q geometry common.large_distance a ha).trans (Q_le_adjacent_h R hb hab)
  rw [← common.centralizer c b hc (adjacent_symm R hbc)]
  rw [← inf_assoc, inf_eq_left.mpr hVQ]

include common in
/-- The neighboring edge kernel bounds the radius-intersection index by four. -/
theorem radius_inf_kernel_index_le_four [Finite M] (radius : RadiusFacts R geometry)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) :
    (V R a ⊓ Q R c).relIndex (V R a) ≤ 4 := by
  obtain ⟨b, hab, hbc⟩ := distance_two_neighbor hd
  have hc := distance_two_color ha hd
  have hb : color R b = true := by
    have hh := adjacent_color_ne R hab
    cases h : color R b <;> simp_all
  have hVQ : V R a ≤ Q R b :=
    (Flags.V_le_Q geometry common.large_distance a ha).trans (Q_le_adjacent_h R hb hab)
  have hi := radius.edge_Q_index c b hc (adjacent_symm R hbc)
  rw [inf_relIndex_left]
  exact (relIndex_le_of_le_right hVQ (by rw [hi]; decide)).trans_eq hi

include common in
/-- Normality is relative to the radius group, using its derived subgroup U_a. -/
theorem radius_inf_kernel_normal (radius : RadiusFacts R geometry)
    {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) :
    ((V R a ⊓ Q R c).subgroupOf (V R a)).Normal := by
  have hc := distance_two_color ha hd
  have hZQ : Z R a ≤ Q R c := by
    rw [← common.X_eq_Z a ha]
    apply common.X_bound a ha c hc
    rw [hd, geometry.distance_constant a ha]
    exact common.large_distance
  apply Normal.of_commutator_le
  intro x hx
  have hm := mem_map_of_mem (V R a).subtype hx
  rw [map_subtype_commutator, radius.radius_derived a ha] at hm
  exact ⟨x.property, hZQ (DistanceEight.U_le_Z R a hm)⟩

include common in
/-- The escape clause makes every critical midpoint a noncentral radius generator. -/
theorem midpoint_nu [Finite M] (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    nu R geometry (alpha R) s.middle := by
  refine ⟨(cosetGraph R).dist_comm.trans s.first_distance, ?_⟩
  intro hB
  apply midpoint_escape source common hb s
  have hcomm : V R (alpha R) ≤ centralizer (Z R s.middle : Set (FreeAmalgam R)) := by
    rw [radius.B_eq_center (alpha R) rfl] at hB
    intro x hx z hz
    obtain ⟨v, hv, rfl⟩ := hB hz
    exact (congrArg Subtype.val ((mem_center_iff.mp hv) ⟨x, hx⟩)).symm
  have h := radius_inf_kernel common rfl s.first_distance
  rw [inf_eq_left.mpr hcomm] at h
  exact inf_eq_left.mp h

include common in
/-- The critical midpoint gives a nontrivial quotient of order at most four. -/
theorem midpoint_intersection_index_bounds [Finite M] (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    2 ≤ (V R (alpha R) ⊓ Q R s.middle).relIndex (V R (alpha R)) ∧
      (V R (alpha R) ⊓ Q R s.middle).relIndex (V R (alpha R)) ≤ 4 := by
  have hi := radius_inf_kernel_index_le_four common radius rfl s.first_distance
  have hn : (V R (alpha R) ⊓ Q R s.middle).relIndex (V R (alpha R)) ≠ 0 := by
    let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
    let : Finite (V R (alpha R)) := Finite.of_injective
      (inclusion (geometry.V_local (alpha R) rfl common.large_distance)) (inclusion_injective _)
    exact Subgroup.index_ne_zero_of_finite
  have h1 : (V R (alpha R) ⊓ Q R s.middle).relIndex (V R (alpha R)) ≠ 1 := by
    intro h
    exact midpoint_escape source common hb s (((relIndex_eq_one.mp h).trans inf_le_right))
  exact ⟨by omega, hi⟩

/-- The conjugate span at distance two contains the full Z-layer at alpha. -/
theorem Z_le_orbitSpan_of_distance_two [Finite M] (c : Vertex R)
    (hd : (cosetGraph R).dist (alpha R) c = 2) :
    Z R (alpha R) ≤ orbitSpan c := by
  obtain ⟨b, hab, hbc⟩ := distance_two_neighbor hd
  have hc := distance_two_color rfl hd
  have hb : color R b ≠ false := by
    exact (adjacent_color_ne R hab).symm
  have hZb : Z R b = edgeOmega R b := by rw [Z, if_neg hb]
  have heb : edgeOmega R b ≤ orbitSpan c := by
    rw [← hZb]
    exact (Flags.edge_Z_le c b hc (adjacent_symm R hbc)).trans (Z_le_orbitSpan c)
  rw [Z, if_pos (show color R (alpha R) = false from rfl)]
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R (alpha R) hab ht
  rw [← hgt, edgeOmega_act]
  have hn := orbitSpan_normalized c ((stabilizer R (alpha R)).inv_mem hg)
  rw [mem_normalizer_iff_map_conj_eq] at hn
  exact (map_mono heb).trans_eq hn

include common in
/-- The critical midpoint span cannot be contained in Z_alpha. -/
theorem midpoint_span_not_le_Z [Finite M] (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    ¬ orbitSpan s.middle ≤ Z R (alpha R) := by
  intro h
  apply (midpoint_nu common radius hb s).2
  exact (Z_le_orbitSpan s.middle).trans (h.trans
    (Flags.Z_le_B geometry (alpha R)
      (geometry.V_local (alpha R) rfl common.large_distance)))

/-- The large-intersection hypothesis forces Z_c itself out of Z_alpha. -/
theorem large_intersection_not_le_Z (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection) :
    ¬ Z R s.middle ≤ Z R (alpha R) := by
  intro h
  apply hs
  change ⁅V R (alpha R) ⊓ Q R s.middle, V R s.middle⁆ ≤ _
  rw [commutator_comm]
  exact ((commutator_mono le_rfl inf_le_right).trans
    (radius.commutator_le_Z s.middle s.middle_color)).trans h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne
