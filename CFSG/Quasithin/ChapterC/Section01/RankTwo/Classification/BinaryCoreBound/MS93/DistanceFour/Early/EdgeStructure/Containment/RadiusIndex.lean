module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.PairedSpans
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.OrderTwo.Offender

/-!
# The radius-index obstruction for an escaping neighbor

The escaping neighbor has a central kernel displacement. If V_alpha' lay
in U_alpha, its commutator with the seed would lie both in the natural
subgroup and in the local fixed subgroup, and hence vanish. This would
put the escaping edge displacement in the radius center and then B_alpha.
Consequently no actual radius offender can exist at that vertex.

For the paired critical path, an image of V_alpha of order at most two in
the opposite local quotient would make Z_alpha' such an offender. This
proves the strict radius-image inequality in the second paragraph of
(4.6.4). It does not yet prove the subsequent intersection index for the
two adjacent Z-layers.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.2)--(4.6.4), printed pp.901--902. All fixed indices refer to
the actual V_alpha/Z_alpha action, and Frattini is intrinsic to the actor.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- A bad neighbor excludes the natural derived-radius conclusion of (4.6.2).
Its central kernel displacement would otherwise centralize the entire radius. -/
theorem escaping_radius_derived_not_le_natural (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ¬ ⁅V R a,V R a⁆ ≤ U R a := by
  intro hderived
  have hg := escaping_neighbor_geometry common initial a b d ha hab hdb hbad
  have hZd : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hg.2.1.le le_rfl)
  have hcent : ⁅Z R d,Q R a⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
    rintro x hx y hy
    obtain ⟨z,hz,rfl⟩ :=
      escaping_neighbor_commutator_le_local_center common initial hb a b d ha hab hdb hbad hx
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)
  have hzero : ⁅Z R d,V R a⁆ = ⊥ := le_bot_iff.mp
    ((le_inf ((commutator_mono hZd le_rfl).trans hderived)
      (((commutator_mono le_rfl (radius_le_Q common a ha)).trans hcent).trans
        (centralizer_le (Ltilde_le_stabilizer a)))).trans
          (Flags.U_fixed_eq_bot common a ha).le)
  have hlocal : Z R d ≤ (center (V R a)).map (V R a).subtype := by
    intro z hz
    refine ⟨⟨z,hZd hz⟩,mem_center_iff.mpr ?_,rfl⟩
    intro v
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hzero) hz v v.property)
  exact hbad ((edge_commutator_le_natural common d b hg.1 hdb).trans
    ((U_le_Z d).trans (hlocal.trans (initial.center_le_B a ha))))

include common in
/-- Every eligible actual radius offender is excluded at a vertex with a
bad neighbor. The actor, intrinsic Frattini group and fixed quotient remain
literal subgroups of the source amalgam. -/
theorem escaping_neighbor_not_offender (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (t : Vertex R) (hat : Adjacent R a t) (A : Subgroup (FreeAmalgam R))
    (hAt : A ≤ Q R t) (hAa : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a) :
    ¬ (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A := by
  intro hi
  exact escaping_radius_derived_not_le_natural common initial hb a b d ha hab hdb hbad
    (initial.offender_derived_le a t ha hat A hAt hAa hPhi hi)

include common in
/-- The radius image in the opposite local quotient has order greater than
two. Otherwise the critical endpoint is an actual offender, contradicting
the bad-neighbor obstruction. This is the middle comparison on p.902. -/
theorem two_lt_paired_radius_image (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d,Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (p : SpanOffender.PairedSpans geometry a b d ha) :
    2 < (Q R p.e).relIndex (V R a) := by
  by_contra! hsmall
  obtain ⟨t,hat,hAt,hAa,hPhi⟩ := OrderTwo.critical_actor common a p.r ha p.critical
  have hcomm : ⁅V R a ⊓ Q R p.e,Z R p.r⁆ ≤ Z R a := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans (p.layer_right.trans inf_le_left)
  have hAG : Z R p.r ≤ stabilizer R a := p.seed_edge.trans
    (fun _ hx => hx.2 a (adjacent_symm R hab))
  have hfix := OrderTwo.fixed_index_le_of_commutator common a p.e ha (Z R p.r) hAG hcomm
  let := finite_stabilizer R p.r
  let : Finite (Z R p.r) := Finite.of_injective (inclusion (Z_le_stabilizer R p.r))
    (inclusion_injective _)
  have hnonzero : (Q R a).relIndex (Z R p.r) ≠ 0 := index_ne_zero_of_finite
  have hnotone : (Q R a).relIndex (Z R p.r) ≠ 1 := fun hi => hAa (relIndex_eq_one.mp hi)
  exact escaping_neighbor_not_offender common initial hb a b d ha hab hdb hbad
    t hat (Z R p.r) hAt hAa hPhi (by omega)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
