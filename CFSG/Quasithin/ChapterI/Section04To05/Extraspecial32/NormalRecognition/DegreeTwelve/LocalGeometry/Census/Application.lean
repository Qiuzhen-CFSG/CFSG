module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry

/-!
# Application of the census assembly to the selected intersection

The census uses containment in the literal original core. The selected
intersection provides this containment by its first projection. The completed
census discharges the local-census premise of the published geometry
constructor. The selected configuration and second-centralizer alternatives
retain their independent producers.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 4.1–4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Consumer application with the actual `Q ∩ gQg⁻¹`. The orbit profile and
outside-product count are still premises to be discharged by their producers. -/
public theorem nonempty_sourceGeometry_of_census_orbits (h : Hypotheses z)
    (d : FusionEightData z) (a : SelectedFusionData h) (o : Census.OrbitData z a.u)
    (hp : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      Nat.card (Census.OutsideProducts z t) = 16)
    (hb : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      (∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) →
      SecondCentralizerAlternative z t) : Nonempty (SourceGeometry h) := by
  apply nonempty_sourceGeometry_of_local_inputs h d a ?_ hb
  intro t htE ht hnt
  exact Census.localInvolutionCensus_of_orbits_of_outside_count h d a o
    htE.1 ht hnt (hp t htE ht hnt)

/-- The completed census at the literal `Q ∩ gQg⁻¹`, with all orbit and
product premises discharged. Selection and the second-centralizer alternatives
are the independent inputs retained by the source-geometry assembly. -/
public theorem nonempty_sourceGeometry_of_census (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h)
    (hb : ∀ t : G, t ∈ coreIntersection z a.g → orderOf t = 2 → ¬ IsConj z t →
      (∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x) →
      SecondCentralizerAlternative z t) : Nonempty (SourceGeometry h) := by
  apply nonempty_sourceGeometry_of_local_inputs h d a ?_ hb
  intro t htE ht hnt
  exact Census.localInvolutionCensus_of_quaternion_normal h hn d a htE.1 ht hnt

end CFSG.Quasithin.Extraspecial32.DegreeTwelve
