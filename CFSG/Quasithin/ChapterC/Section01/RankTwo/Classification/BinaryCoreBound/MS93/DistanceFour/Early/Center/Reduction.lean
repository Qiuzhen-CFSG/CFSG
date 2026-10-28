module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.Radius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Closing the radius-center argument from edge placement

The actual quotient-fixed preimage B_a is covariant under the amalgam action.
If B_a lies in one incident edge radius V_b, the vertex stabilizer puts it in
every incident edge radius. These edge radii are abelian and contain all the
generators of V_a. Hence B_a is central in V_a. More generally, centralizing
one incident edge radius suffices. Under center failure this also selects
a neighbor d of that edge with [B_a,Z_d] nontrivial, as in the first sentence
of the source proof.

Failure of this containment in the center also transports between M-vertices.
Consequently, under failure at a, it suffices to find a neighbor d of an
incident edge b with B_d contained in V_b. This is precisely the final
containment obtained by the fixed-quotient calculation in (4.6.7). That
calculation remains an explicit premise here; the initial center inclusion
supplies the other direction of the equality.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.7), printed p.904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
open Initial NaturalStructure.Exclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Centralizing one incident edge radius forces B to centralize the full radius. -/
theorem B_le_radius_center_of_centralizes_edge (common : CommonFacts R source geometry)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hB : B R a (geometry.Z_normal a) ≤ centralizer (V R b : Set (FreeAmalgam R))) :
    B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype := by
  have hnear (t : Vertex R) (hat : Adjacent R a t) :
      B R a (geometry.Z_normal a) ≤ centralizer (V R t : Set (FreeAmalgam R)) := by
    obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R a hab hat
    have hfix : act R g a = a := hg
    have hcov := Escape.PairingControl.FirstPairing.B_act
      (geometry := geometry) common.large_distance g a ha
    rw [hfix] at hcov
    rw [← hgt, V_act, hcov]
    exact (map_mono hB).trans (map_centralizer_le_centralizer_image _ _)
  have hcentral : B R a (geometry.Z_normal a) ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    apply radius_le_of_generators a ha
    intro d hd hdist
    have hda : (cosetGraph R).dist d a = 0 ∨ (cosetGraph R).dist d a = 2 := by
      obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d a
      have hEven : Even p.length := (walk_even_iff_color_eq R p).mpr (hd.trans ha.symm)
      rw [Nat.even_iff] at hEven
      omega
    rcases hda with hzero | htwo
    · have hEq := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
      subst d
      exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
        (centralizer_le ((B_le_radius common a ha).trans (radius_le_Q common a ha)))
    · obtain ⟨t, hdt, hat⟩ := exists_common_neighbor_of_dist_two R d a htwo
      have hdV : Z R d ≤ V R t := le_iSup_of_le d (le_iSup_of_le
        (show (cosetGraph R).dist d t ≤ 2 from
          (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)).le.trans (by decide))
        le_rfl)
      exact hdV.trans (le_centralizer_iff.mp (hnear t hat))
  intro x hx
  refine ⟨⟨x, B_le_radius common a ha hx⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro y
  exact Subtype.ext (hcentral hx y y.property)

/-- Placement in one incident abelian edge radius forces B to centralize the full radius. -/
theorem B_le_radius_center_of_le_edge (common : CommonFacts R source geometry)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hB : B R a (geometry.Z_normal a) ≤ V R b) :
    B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype :=
  B_le_radius_center_of_centralizes_edge common a b ha hab
    (hB.trans (le_centralizer_iff_isMulCommutative.mpr
      (edge_radius_commutative geometry common.large_distance a b ha hab)))

/-- The first selection in (4.6.7), over any prescribed edge at the contrary vertex. -/
theorem exists_noncentral_edge_generator_of_center_failure
    (common : CommonFacts R source geometry)
    (a b : Vertex R) (ha : color R a = false) (hab : Adjacent R a b)
    (hfail : ¬ B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype) :
    ∃ d, Adjacent R d b ∧ ⁅B R a (geometry.Z_normal a), Z R d⁆ ≠ ⊥ := by
  by_contra! h
  apply hfail
  apply B_le_radius_center_of_centralizes_edge common a b ha hab
  apply le_centralizer_iff.mp
  apply radius_le_of_h_neighbors ha hab
  intro d hdb
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (h d hdb))

/-- A failure of radius-center containment transports to every M-vertex. -/
theorem B_center_failure_at (common : CommonFacts R source geometry)
    (a : Vertex R) (ha : color R a = false)
    (hfail : ¬ B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype)
    (c : Vertex R) (hc : color R c = false) :
    ¬ B R c (geometry.Z_normal c) ≤ (center (V R c)).map (V R c).subtype := by
  obtain ⟨u, hu⟩ := exists_mVertex_of_color R ha
  obtain ⟨v, hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by
    rw [hu, act_mVertex]
    simpa only [g, mul_inv_cancel_left] using hv.symm
  rw [← hg, Escape.PairingControl.FirstPairing.B_act common.large_distance g a ha,
    V_act, ← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective,
    map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective]
  exact hfail

/-- The final implication of (4.6.7), retaining its fixed-quotient placement step. -/
theorem B_eq_center_of_failure_edge_placement (common : CommonFacts R source geometry)
    (initial : InitialFacts R geometry)
    (placement : ∀ a b, color R a = false → Adjacent R a b →
      (¬ B R a (geometry.Z_normal a) ≤ (center (V R a)).map (V R a).subtype) →
      ∃ d, Adjacent R d b ∧ B R d (geometry.Z_normal d) ≤ V R b)
    (a : Vertex R) (ha : color R a = false) :
    B R a (geometry.Z_normal a) = (center (V R a)).map (V R a).subtype := by
  apply le_antisymm _ (initial.center_le_B a ha)
  by_contra hfail
  obtain ⟨a', hcrit⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  obtain ⟨b, hab, _⟩ := exists_adjacent_dist_sub_one R a a' (by
    rw [hcrit.1, geometry.distance_constant a ha]
    exact lt_trans (by decide : 0 < 2) common.large_distance)
  obtain ⟨d, hdb, hB⟩ := placement a b ha hab hfail
  have hd : color R d = false := by
    have hb := adjacent_color_ne R hab
    have hd := adjacent_color_ne R hdb
    cases hc : color R b <;> cases he : color R d <;> simp_all
  exact B_center_failure_at common a ha hfail d hd
    (B_le_radius_center_of_le_edge common d b hd hdb hB)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
