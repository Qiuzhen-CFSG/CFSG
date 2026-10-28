module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths

/-!
# The reversed radius supplement for the second section

Index four in the first section supplies a radius generator escaping the
midpoint kernel. Critical reversal and transport of the midpoint edge give
another genuine critical segment; the accepted displacement theorem then
computes the reversed index. Relative normality and the edge index show
`V_c Q_alpha = Q_beta`, with an explicit product decomposition.

The early radius commutator bound gives `[K,V_c] ≤ Z_c`. The supplement
therefore gives `[K,Q_beta] ≤ Z_c Z_alpha`. Both central layers commute
with the edge kernel modulo `Z_alpha`, so `[K,Q_beta] ≤ Y`. Consequently
the actual edge kernel acts trivially on the literal second linear section.
None of these deductions uses the small/large intersection alternative.
The cubic fixed-space argument remains separate.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(2), printed p.910, using (4.6.9), printed p.908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
  (f : Frame source) (hb : geometry.b R = 4) (s : CriticalSegment geometry)
  (hbc : Adjacent R (beta R) s.middle)

include common radius f hb hbc in
/-- The reversed midpoint has the same index four, via a transported critical segment. -/
theorem reversed_midpoint_index_four :
    (Q R (alpha R)).relIndex (V R s.middle) = 4 := by
  have hnot : ¬ V R (alpha R) ≤ Q R s.middle := by
    intro h
    have hindex := intersection_index_four common radius f hb s hbc
    have he : intersection s.middle = V R (alpha R) := inf_eq_left.mpr h
    rw [he, relIndex_self] at hindex
    omega
  obtain ⟨d, hd, hda, hcrit⟩ :=
    DistanceEight.PathCentrality.exists_critical_shift R rfl
      (show (cosetGraph R).dist (alpha R) s.middle + 2 = geometry.b R by
        rw [s.first_distance, hb]) hnot
  have hreverse := common.critical_reverse d hd s.middle s.middle_color hcrit
  obtain ⟨g, hg | hg⟩ := edge_transitive R (adjacent_symm R hbc) (base_adjacent R)
  · have hstart : act R g s.middle = alpha R := hg.1
    have hedge : act R g (beta R) = beta R := hg.2
    let t : CriticalSegment geometry := {
      endpoint := act R g d
      middle := act R g (alpha R)
      critical := by
        constructor
        · change (cosetGraph R).dist (alpha R) (act R g d) = geometry.b R
          rw [← hstart, dist_act, hreverse.1, geometry.distance_constant s.middle s.middle_color]
          exact geometry.distance_constant (alpha R) rfl
        · rw [← hstart, Z_act, Q_act]
          exact fun h => hreverse.2
            ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h)
      first_distance := by
        calc
          _ = (cosetGraph R).dist (act R g s.middle) (act R g (alpha R)) := by rw [hstart]
          _ = _ := dist_act R g _ _
          _ = 2 := by rw [SimpleGraph.dist_comm, s.first_distance]
      second_distance := by
        rw [dist_act, SimpleGraph.dist_comm, hda] }
    have htbc : Adjacent R (beta R) t.middle := by
      change Adjacent R (beta R) (act R g (alpha R))
      have he := (adjacent_act_iff R g _ _).mpr (adjacent_symm R (base_adjacent R))
      change Adjacent R (act R g (beta R)) (act R g (alpha R)) at he
      rwa [hedge] at he
    have hindex := (displacement_cardinalities source geometry common hb radius.toEarlyFacts
      f.flagControl t.middle t.first_distance htbc
      (midpoint_displacement_noncentral common radius hb t)).2.2.2
    change (Q R (act R g (alpha R))).relIndex (V R (alpha R)) = 4 at hindex
    have hV : V R (alpha R) = (V R s.middle).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [← V_act, hstart]
    rw [hV, Q_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hindex
    exact hindex
  · have hc := action_preserves_color R g s.middle
    rw [hg.1, s.middle_color] at hc
    cases hc

include common radius f hb hbc in
/-- The midpoint radius supplements the original vertex kernel in the edge kernel. -/
theorem midpoint_radius_supplement :
    V R s.middle ⊔ Q R (alpha R) = Q R (beta R) := by
  have hV : V R s.middle ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ s.middle_color).trans
      (Q_le_adjacent_h R rfl (adjacent_symm R hbc))
  have hQ : Q R (alpha R) ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (base_adjacent R)
  have hsup := sup_le hV hQ
  have hnorm : Q R (beta R) ≤ normalizer (Q R (alpha R)) :=
    (show Q R (beta R) ≤ stabilizer R (alpha R) from
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Q_normalized R _)
  let : ((Q R (alpha R)).subgroupOf (Q R (beta R))).Normal :=
    normal_subgroupOf_of_le_normalizer hnorm
  have hrel := relIndex_sup_right ((V R s.middle).subgroupOf (Q R (beta R)))
    ((Q R (alpha R)).subgroupOf (Q R (beta R)))
  rw [← subgroupOf_sup hV hQ, relIndex_subgroupOf hsup, relIndex_subgroupOf hV,
    reversed_midpoint_index_four common radius f hb s hbc] at hrel
  have htower := relIndex_mul_relIndex (Q R (alpha R))
    (V R s.middle ⊔ Q R (alpha R)) (Q R (beta R)) le_sup_right hsup
  rw [hrel, radius.toEarlyFacts.edge_Q_index (alpha R) (beta R) rfl (base_adjacent R)] at htower
  exact le_antisymm hsup (relIndex_eq_one.mp (by omega))

include common radius f hb hbc in
/-- The supplement is a genuine product: normality is relative to the edge kernel. -/
theorem midpoint_radius_product (x : FreeAmalgam R) (hx : x ∈ Q R (beta R)) :
    ∃ v ∈ V R s.middle, ∃ q ∈ Q R (alpha R), v * q = x := by
  have hV : V R s.middle ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance _ s.middle_color).trans
      (Q_le_adjacent_h R rfl (adjacent_symm R hbc))
  have hQ : Q R (alpha R) ≤ Q R (beta R) :=
    Q_le_adjacent_h R rfl (base_adjacent R)
  let : ((Q R (alpha R)).subgroupOf (Q R (beta R))).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((show Q R (beta R) ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Q_normalized R _))
  have hx' : (⟨x, hx⟩ : Q R (beta R)) ∈
      (V R s.middle).subgroupOf (Q R (beta R)) ⊔
        (Q R (alpha R)).subgroupOf (Q R (beta R)) := by
    rw [← subgroupOf_sup hV hQ, midpoint_radius_supplement common radius f hb s hbc,
      subgroupOf_self]
    trivial
  obtain ⟨v, hv, q, hq, he⟩ := mem_sup_of_normal_right.mp hx'
  exact ⟨v, hv, q, hq, congrArg Subtype.val he⟩

include radius in
omit [Finite M] in
/-- The first printed commutator bound uses the literal intersection with Q_c. -/
theorem intersection_commutator_midpoint_le :
    ⁅intersection s.middle, V R s.middle⁆ ≤ Z R s.middle := by
  rw [commutator_comm]
  exact (commutator_mono le_rfl inf_le_right).trans
    (radius.toEarlyFacts.commutator_le_Z _ s.middle_color)

include common radius f hb hbc in
/-- The supplement bounds the whole edge displacement by the two central layers. -/
theorem intersection_commutator_edge_le_sup :
    ⁅intersection s.middle, Q R (beta R)⁆ ≤ Z R s.middle ⊔ Z R (alpha R) := by
  let W := Z R s.middle ⊔ Z R (alpha R)
  have hnorm : Q R (beta R) ≤ normalizer W := by
    apply le_trans _ (normalizer_inf_normalizer_le_normalizer_sup _ _)
    apply le_inf
    · exact (show Q R (beta R) ≤ stabilizer R s.middle from
        fun _ hx => hx.2 _ hbc).trans (Z_normalized R _)
    · exact (show Q R (beta R) ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))).trans (Z_normalized R _)
  have hpre : Q R (beta R) ≤ commutatorPreimage (Q R (beta R)) (intersection s.middle) W := by
    rw [← midpoint_radius_supplement common radius f hb s hbc]
    apply sup_le
    · apply le_commutatorPreimage le_sup_left
      rw [commutator_comm]
      exact (intersection_commutator_midpoint_le radius s).trans le_sup_left
    · apply le_commutatorPreimage le_sup_right
      rw [commutator_comm]
      exact ((commutator_mono inf_le_left le_rfl).trans
        (radius.toEarlyFacts.commutator_le_Z (alpha R) rfl)).trans le_sup_right
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)

include radius in
omit [Finite M] in
private theorem edge_commutator_bound (a b : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) : ⁅Z R a, Q R b⁆ ≤ Z R b := by
  apply commutator_le_of_normalized_index_two _ _ _
    (Flags.edge_Z_le a b ha hab) (radius.toEarlyFacts.edge_Z_index a b ha hab)
  · exact (show Q R b ≤ stabilizer R a from
      fun _ hx => hx.2 _ (adjacent_symm R hab)).trans (Z_normalized R _)
  · exact (show Q R b ≤ stabilizer R b from fun _ hx => hx.1).trans (Z_normalized R _)

include common radius hbc in
omit [Finite M] in
/-- The two central layers commute with the edge kernel modulo Z_alpha. -/
theorem midpoint_sup_commutator_edge_le_Z :
    ⁅Z R s.middle ⊔ Z R (alpha R), Q R (beta R)⁆ ≤ Z R (alpha R) := by
  have hZcV : Z R s.middle ≤ V R (alpha R) :=
    le_iSup_of_le s.middle (le_iSup_of_le
      (by rw [SimpleGraph.dist_comm, s.first_distance]) le_rfl)
  have hnorm : V R (alpha R) ≤ normalizer (Z R (alpha R)) :=
    (geometry.V_local (alpha R) rfl common.large_distance).trans (Z_normalized R _)
  have hpre : Z R s.middle ⊔ Z R (alpha R) ≤
      commutatorPreimage (V R (alpha R)) (Q R (beta R)) (Z R (alpha R)) := by
    apply sup_le
    · apply le_commutatorPreimage hZcV
      exact (edge_commutator_bound radius _ _ s.middle_color
        (adjacent_symm R hbc)).trans (Flags.edge_Z_le _ _ rfl (base_adjacent R))
    · apply le_commutatorPreimage (Z_le_VBall R (alpha R) 2)
      exact (edge_commutator_bound radius _ _ rfl (base_adjacent R)).trans
        (Flags.edge_Z_le _ _ rfl (base_adjacent R))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)

include common radius f hb hbc in
/-- The edge displacement lies in the actual denominator Y of the second section. -/
theorem intersection_commutator_edge_le_fixedPreimage :
    ⁅intersection s.middle, Q R (beta R)⁆ ≤ fixedPreimage s.middle := by
  apply le_commutatorPreimage
  · exact le_normalizer_iff_commutator_le_left.mp (edge_normalizes_intersection hbc)
  · exact (commutator_mono (intersection_commutator_edge_le_sup common radius f hb s hbc)
      le_rfl).trans (midpoint_sup_commutator_edge_le_Z common radius s hbc)

include common radius f hb hbc in
/-- The edge kernel acts trivially on the exact quotient (K/Z_alpha)/(Y/Z_alpha). -/
theorem secondRepresentation_kernel_contains_edge (d : LayerModule source (V R (alpha R))) :
    (Q R (beta R)).subgroupOf (flagResidual source f.orientation) ≤
      (secondRepresentation common radius f s hbc d).ker := by
  have hqker := d.sectionMap_kernel (intersection s.middle) (fixedPreimage s.middle)
    inf_le_left (Z_le_fixedPreimage common s.first_distance)
  intro g hg
  apply LinearMap.ext
  intro z
  obtain ⟨v, hv⟩ := d.sectionMap_surjective (intersection s.middle) (fixedPreimage s.middle)
    inf_le_left (Multiplicative.ofAdd z)
  have hn : (g : FreeAmalgam R) ∈ normalizer (intersection s.middle) :=
    edge_normalizes_intersection hbc hg
  let w : intersection s.middle := ⟨g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
    (mem_normalizer_iff.mp hn v).mp v.property⟩
  have hmem : w * v⁻¹ ∈
      (d.sectionMap (intersection s.middle) (fixedPreimage s.middle) inf_le_left).ker := by
    rw [hqker]
    change ⁅(g : FreeAmalgam R), (v : FreeAmalgam R)⁆ ∈ fixedPreimage s.middle
    apply intersection_commutator_edge_le_fixedPreimage common radius f hb s hbc
    rw [commutator_comm]
    exact commutator_mem_commutator hg v.property
  have hqw : d.sectionMap (intersection s.middle) (fixedPreimage s.middle) inf_le_left w =
      d.sectionMap (intersection s.middle) (fixedPreimage s.middle) inf_le_left v := by
    change d.sectionMap (intersection s.middle) (fixedPreimage s.middle) inf_le_left (w * v⁻¹) = 1 at hmem
    rwa [map_mul, map_inv, mul_inv_eq_one] at hmem
  have ha := secondRepresentation_action common radius f s hbc d g v w rfl
  rw [hqw, hv] at ha
  exact ha.symm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
