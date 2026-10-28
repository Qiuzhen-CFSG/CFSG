module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction.IndexTwo.FixedCore

/-!
# Escape from the conjugate kernel in MS93 (4.4.2)

Put c = (a+2)^g. The established nontriviality of R₁ gives a generator
Z_d of the span of Z_a under G_c which does not centralize Zδ. Here
d(d,c) = 2 and d(δ,c) ≤ b-2. Thus Zδ is not contained in Q_d, and
critical-distance minimality forces d(δ,d) = b. Consequently c is exactly
two steps before d on this critical pair, so (4.3) gives Vδ not contained
in Q_c. The proof below uses the contrapositive at each generator.

The natural centralizer equivalence then gives the printed noncommutation
[Z_(a+2)^g,Vδ] ≠ 1. Once R₁ ≠ 1 is supplied by FixedCore, this step needs
neither of the failed forward/reverse escape assumptions. All groups and
conjugations remain those of the retained Configuration and its right action.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.2), printed p.893, the sentence invoking (4.3) after R₁ ≠ 1.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace Configuration
variable {a a' : Vertex R} {p : CriticalPath R geometry a a'}

/-- Source (4.3) applied to a genuine critical endpoint detected by R₁.
The conjugate vertex is its predecessor at distance two, not a critical
endpoint itself. Joint normality and local control supply R₁ ≠ 1. -/
theorem radius_not_le_conjugate_kernel (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ¬ V R s.delta ≤ Q R s.conjugateSecond := by
  have hl := p.length_eq_b
  have hga : act R s.g a = a := s.mem_stabilizer
  have hac : (cosetGraph R).dist a s.conjugateSecond = 2 := by
    change (cosetGraph R).dist a (act R s.g (p.walk.getVert 2)) = 2
    simpa only [hga, p.dist_start (by omega : 2 ≤ p.walk.length)] using
      dist_act R s.g a (p.walk.getVert 2)
  have hspan : (localZSpan R a (p.walk.getVert 2)).map
      (MulAut.conj s.g⁻¹).toMonoidHom = localZSpan R a s.conjugateSecond := by
    rw [← LocalCommutator.CriticalCase.localZSpan_act, hga]
    rfl
  have hnear : (cosetGraph R).dist s.delta s.conjugateSecond ≤ geometry.b R - 2 := by
    rw [SimpleGraph.dist_comm]
    exact s.conjugateSecond_distance hb
  intro htrap
  apply s.firstCommutator_ne_bot hb common hlocal hnorm
  rw [firstCommutator, hspan]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply iSup_le
  intro t
  have htc : act R t s.conjugateSecond = s.conjugateSecond := t.property
  have hdist : (cosetGraph R).dist s.conjugateSecond (act R t a) = 2 := by
    have hh := dist_act R (t : FreeAmalgam R) s.conjugateSecond a
    simpa only [htc, SimpleGraph.dist_comm (u := s.conjugateSecond), hac] using hh
  have hQ : Z R s.delta ≤ Q R (act R t a) := by
    by_contra hn
    have hmin := criticalDistance_le R s.delta (geometry.exists_critical _ s.delta_color) hn
    rw [geometry.distance_constant _ s.delta_color] at hmin
    change geometry.b R ≤ _ at hmin
    have htri := (cosetGraph_connected R).dist_triangle
      (u := s.delta) (v := s.conjugateSecond) (w := act R t a)
    have hcrit : CriticalPair R s.delta (act R t a)
        (geometry.exists_critical _ s.delta_color) := by
      refine ⟨?_, hn⟩
      rw [geometry.distance_constant _ s.delta_color]
      change _ = geometry.b R
      omega
    exact common.escape s.delta s.delta_color (act R t a) hcrit s.conjugateSecond
      hdist (by omega) htrap
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact le_bot_iff.mp ((commutator_mono le_rfl hQ).trans_eq
    (geometry.centralizes _ ((action_preserves_color R t a).trans p.start_color)))

/-- The conjugate noncommutation used in the R₁ argument of MS93 (4.4.2),
with every premise beyond the original fixed-core inputs discharged. -/
theorem conjugate_noncommutation (s : Configuration p)
    (hb : 4 < geometry.b R) (common : CommonFacts R source geometry)
    (hlocal : LocalCommutatorControl R)
    (hnorm : stabilizer R a ≤ normalizer (jointSpan p)) :
    ⁅Z R s.conjugateSecond, V R s.delta⁆ ≠ ⊥ :=
  (s.conjugate_noncommutation_iff_radius_not_le_kernel hb common).mpr
    (s.radius_not_le_conjugate_kernel hb common hlocal hnorm)

end Configuration
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.OrbitEscape.CommutatorContradiction
