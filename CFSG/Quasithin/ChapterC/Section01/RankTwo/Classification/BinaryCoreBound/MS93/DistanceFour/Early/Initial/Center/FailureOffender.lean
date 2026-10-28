module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.FailureOffender.Index
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.FailureOffender.Intersection
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The reciprocal index argument for the radius center quotient

Compare the displacement indices of the two radius groups at distance two.
The favorable side supplies an offender using its escaping generators. If
the other side is favorable, conjugate its actor and commutator bound to the
prescribed vertex before constructing the literal quotient action there.

On a critical path of length four, the common escape and reversal facts
supply both nontrivial actor images. The imported natural-module argument
derives both per-generator intersection bounds from center failure. Combining
these facts constructs an offender on the literal quotient V_a/Z(V_a),
with elementary nontrivial image under the marked projection with kernel Q_a.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), first paragraph of (4.6.1), printed p.900.
-/


@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem radius_intersection_bound_act
    (a c : Vertex R) (E : Subgroup (FreeAmalgam R)) (g : FreeAmalgam R)
    (h : ⁅V R a ⊓ Q R c, E⁆ ≤ (center (V R a)).map (V R a).subtype) :
    ⁅V R (act R g a) ⊓ Q R (act R g c), E.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤
      (center (V R (act R g a))).map (V R (act R g a)).subtype := by
  rw [V_act, Q_act, ← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective,
    ← map_inf _ _ _ (MulAut.conj g⁻¹).injective, ← map_commutator]
  exact map_mono h

/-- Reciprocal source bounds give an offender at the prescribed vertex,
regardless of which direction has the smaller displacement index. -/
theorem radiusCenterOffender_of_reciprocal_generator_bounds
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a c : Vertex R) (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hanot : ¬ V R a ≤ Q R c) (hcnot : ¬ V R c ≤ Q R a)
    (hforward : RadiusCenterIntersectionBound a c)
    (hreverse : RadiusCenterIntersectionBound c a) :
    HasRadiusCenterOffender common hb a ha := by
  have hd' : (cosetGraph R).dist c a = 2 := by rw [SimpleGraph.dist_comm, hd]
  have hane : ¬ radiusEscapeActor c a ≤ Q R c := by
    intro h
    apply hanot
    have hs := radiusEscapeActor_sup_Q c a ha
    rw [sup_eq_right.mpr h] at hs
    exact le_sup_left.trans hs.ge
  have hcne : ¬ radiusEscapeActor a c ≤ Q R a := by
    intro h
    apply hcnot
    have hs := radiusEscapeActor_sup_Q a c hc
    rw [sup_eq_right.mpr h] at hs
    exact le_sup_left.trans hs.ge
  by_cases hi : (Q R c).relIndex (V R a) ≤ (Q R a).relIndex (V R c)
  · apply radiusCenterOffender_of_intersection_bound common hb a c ha hc hd
      (radiusEscapeActor a c) (radiusEscapeActor_le a c) hcne
      (radiusEscapeActor_commutator common a c ha hc hd hforward)
    rwa [radiusEscapeActor_relIndex common a c ha hc hd]
  · obtain ⟨u, hu⟩ := exists_mVertex_of_color R hc
    obtain ⟨v, hv⟩ := exists_mVertex_of_color R ha
    let g := u⁻¹ * v
    have hg : act R g c = a := by
      rw [hu, act_mVertex]
      simpa only [g, mul_inv_cancel_left] using hv.symm
    let E := (radiusEscapeActor c a).map (MulAut.conj g⁻¹).toMonoidHom
    have hcolor : color R (act R g a) = false := by rw [action_preserves_color, ha]
    have hdist : (cosetGraph R).dist a (act R g a) = 2 := by
      calc
        _ = (cosetGraph R).dist (act R g c) (act R g a) := by rw [hg]
        _ = (cosetGraph R).dist c a := dist_act R g c a
        _ = 2 := hd'
    have hEV : E ≤ V R (act R g a) := by
      rw [V_act]
      exact map_mono (radiusEscapeActor_le c a)
    have hne : ¬ E ≤ Q R a := by
      intro h
      have h' : E ≤ Q R (act R g c) := by simpa only [hg] using h
      rw [Q_act] at h'
      exact hane ((map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h')
    have hcomm : ⁅V R a ⊓ Q R (act R g a), E⁆ ≤
        (center (V R a)).map (V R a).subtype := by
      have hmap := radius_intersection_bound_act c a (radiusEscapeActor c a) g
        (radiusEscapeActor_commutator common c a hc ha hd' hreverse)
      rw [hg] at hmap
      exact hmap
    apply radiusCenterOffender_of_intersection_bound common hb a (act R g a) ha
      hcolor hdist E hEV hne hcomm
    have hcmp : (Q R (act R g a)).relIndex (V R (act R g c)) ≤
        (Q R (act R g c)).relIndex E := by
      rw [Q_act, V_act, Q_act, relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      change _ ≤ ((Q R c).map (MulAut.conj g⁻¹).toMonoidHom).relIndex
        ((radiusEscapeActor c a).map (MulAut.conj g⁻¹).toMonoidHom)
      rw [relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,
        radiusEscapeActor_relIndex common c a hc ha hd']
      omega
    simpa only [hg] using hcmp

/-- The actual critical midpoint supplies both escape premises. The remaining
hypothesis is exactly the pair of source intersection bounds, with no FF
conclusion or additional representation hypothesis hidden in it. -/
theorem radiusCenterOffender_of_critical_generator_bounds
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hbound : ∀ a' c, CriticalPair R a a' (geometry.exists_critical a ha) →
      (cosetGraph R).dist a c = 2 → (cosetGraph R).dist c a' = 2 →
      RadiusCenterIntersectionBound a c ∧ RadiusCenterIntersectionBound c a) :
    HasRadiusCenterOffender common hb a ha := by
  obtain ⟨a', hcrit⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  have hd : (cosetGraph R).dist a a' = 4 := by
    rw [hcrit.1, geometry.distance_constant a ha]
    exact hb
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a a'
  have hleft := SimpleGraph.dist_le (p.take 2)
  have hright := SimpleGraph.dist_le (p.drop 2)
  have hsum := (cosetGraph_connected R).dist_triangle (u := a) (v := p.getVert 2) (w := a')
  have hlen : p.length = 4 := hp.trans hd
  simp only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, hlen] at hleft hright
  have hac : (cosetGraph R).dist a (p.getVert 2) = 2 := by omega
  have hca' : (cosetGraph R).dist (p.getVert 2) a' = 2 := by omega
  have hc : color R (p.getVert 2) = false :=
    (color_eq_of_dist_even R a (p.getVert 2) (by rw [hac]; decide)).symm.trans ha
  have ha' := critical_endpoint_color R a ha _ hcrit
  have hcnot : ¬ V R (p.getVert 2) ≤ Q R a := by
    intro h
    apply (common.critical_reverse a ha a' ha' hcrit).2
    apply le_trans _ h
    exact le_iSup_of_le a' (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hca']) le_rfl)
  obtain ⟨hforward, hreverse⟩ := hbound a' (p.getVert 2) hcrit hac hca'
  exact radiusCenterOffender_of_reciprocal_generator_bounds common hb a (p.getVert 2)
    ha hc hac (common.escape a ha a' hcrit _ hca' (by omega)) hcnot hforward hreverse

/-- The first geometric paragraph of MS93 (4.6.1): failure of radius-center
containment supplies an actual projected offender on V_a/Z(V_a). The natural
module proves both intersection bounds, discharging the conditional index
argument without any assumption that Q_a acts trivially on the quotient. -/
theorem radiusCenterOffender_of_center_failure
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a)) :
    HasRadiusCenterOffender common hb a ha := by
  apply radiusCenterOffender_of_critical_generator_bounds common hb a ha
  intro a' c hcrit hac hca'
  exact radiusCenterIntersectionBounds_of_center_failure source geometry common hb a ha
    hfail a' c hcrit hac hca'

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
