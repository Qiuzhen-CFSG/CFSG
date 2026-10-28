module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.DerivedFixed.Escape

/-!
# Residual fixation under failure of radius-center containment

For a critical path of length four, choose its midpoint c. If V_a' is not
residual-fixed, simultaneous escape supplies a radius generator Z_d whose
center join and displacement are both moved by the critical endpoint.

If Z_d lies in Q_c, the center-failure displacement at a normalizes the
center join, contradicting the first escape. Otherwise transport center
failure to c. Its displacement bound puts [Z_d,V_a] in Z(V_c), which commutes
with the critical endpoint's Z-layer, contradicting the second escape.

This proves the middle paragraph of MS93 (4.6.1). The full center containment
and its independent central-quotient offender remain with the parent owner.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.1), printed pp.900--901.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
open DerivedFixed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Under the contrary center hypothesis in MS93 (4.6.1), simultaneous
conjugate escape forces the local residual to fix the whole radius-derived
subgroup. All normality and generation premises are discharged locally. -/
theorem radius_derived_le_fixed_of_center_failure
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false)
    (hfail : ¬ (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a)) :
    ⁅V R a,V R a⁆ ≤ fixedCore R a := by
  by_contra hnot
  obtain ⟨r,hcrit⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  have hr := critical_endpoint_color R a ha (geometry.exists_critical a ha) hcrit
  have hout := (common.critical_reverse a ha r hr hcrit).2
  have har : (cosetGraph R).dist a r = 4 := by
    rw [hcrit.1, geometry.distance_constant a ha]
    exact hb
  obtain ⟨p,hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a r
  have hlen : p.length = 4 := hp.trans har
  let c := p.getVert 2
  have hleft := SimpleGraph.dist_le (p.take 2)
  have hright := SimpleGraph.dist_le (p.drop 2)
  have hsum := (cosetGraph_connected R).dist_triangle (u := a) (v := c) (w := r)
  simp only [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length, hlen] at hleft hright
  change (cosetGraph R).dist a c ≤ 2 at hleft
  change (cosetGraph R).dist c r ≤ 2 at hright
  have hac : (cosetGraph R).dist a c = 2 := by omega
  have hcr : (cosetGraph R).dist c r = 2 := by omega
  have hc : color R c = false :=
    (color_eq_of_dist_even R a c (by rw [hac]; decide)).symm.trans ha
  obtain ⟨d,hd,hda,hnS,hnK⟩ := simultaneous_generator_escape common a r ha hcrit hnot
  have hbound := center_failure_displacement common hb a c ha hac hfail r hr
    (by rwa [SimpleGraph.dist_comm]) hout
  have hdout : ¬ Z R d ≤ Q R c := by
    intro hdc
    apply hnS
    rw [sup_comm]
    apply Escape.PairingControl.Geometry.LocalProducts.normalizes_sup_of_commutator_le
    · exact (critical_Z_le_stabilizer R geometry a ha
        (by rw [geometry.distance_constant a ha]; exact lt_trans (by decide : 0 < 2) common.large_distance)
        hcrit).trans (radius_center_normalized a)
    · exact (commutator_mono hdc le_rfl).trans hbound
  have hfailc := center_failure_at common a c ha hc hfail
  have hboundc := center_failure_displacement common hb c a hc
    (by rw [SimpleGraph.dist_comm]; exact hac) hfailc d hd hda hdout
  have hK : ⁅Z R d,V R a⁆ ≤ (center (V R c)).map (V R c).subtype := by
    rw [commutator_comm]
    exact (commutator_mono (radius_le_Q common a ha) le_rfl).trans hboundc
  have hZrV : Z R r ≤ V R c := le_iSup_of_le r (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm,hcr]) le_rfl)
  have hcent : ⁅Z R d,V R a⁆ ≤ centralizer (Z R r : Set (FreeAmalgam R)) := by
    rintro x hx z hz
    obtain ⟨v,hv,rfl⟩ := hK hx
    exact congrArg Subtype.val (mem_center_iff.mp hv ⟨z,hZrV hz⟩)
  exact hnK ((le_centralizer_iff.mp hcent).trans (Subgroup.centralizer_le_normalizer _))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
