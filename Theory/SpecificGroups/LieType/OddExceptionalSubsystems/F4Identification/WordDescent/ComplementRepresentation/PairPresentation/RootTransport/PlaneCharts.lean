module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.Geometry
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.PairRoutes
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.MatrixTransport
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport.PlaneCharts.Placement

/-!
# Assembly of literal F4 plane charts from Weyl placement

The pure root-system placement theorem supplies one Weyl word and standard pair
for any two roots. Linearity places the entire plane, the parabolic subsystem
supplies routes in that pair, and integral signed transport gives each original
root parameter its exact matrix value. This proves `HasPairPlaneCharts F` over
every field, including F3, with no independence assumption on the spanning roots.

The final application feeds these charts to the existing plane-relation
consumer. Only its independent completion-level `TransportCoherent` premise
remains; its producer is the separate route-coherence development.

Source: GLS3 §2.9.3, `refs/KGroup/GLS3/chapter2.tex`, lines 1455–1462.
-/

@[expose] public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open PlaneCharts

/-- Whole-plane Weyl placement supplies the exact matrix chart, with all signs
retained. This implication holds over every field, including characteristic three. -/
theorem hasPairPlaneCharts_of_placement (F : Type*) [Field F]
    (hplacement : HasPlanePlacement) : HasPairPlaneCharts F := by
  intro a b
  obtain ⟨w, i, j, ha, hb⟩ := hplacement a b
  refine ⟨w, i, j, fun r t => ?_⟩
  have hr := plane_image_mem_of_generators w a b
    (signedRoot true i) (signedRoot true j) ha hb r
  obtain ⟨v, k, hv⟩ := standardPair_root_route i j (reflectionWord w r.val) hr
  obtain ⟨ε, -, he⟩ := root_conjugate_eq_route F w (pairTransportNodes i j v)
    r.val true (pairNode i j k) hv.symm
  refine ⟨v, true, k, (ε : F) * t, ?_⟩
  change _ = coverEvaluation F (pairInclusion F i j
    (pairTransportRouteWord F v true k ((ε : F) * t)))
  rw [pairInclusion_pairTransportRouteWord]
  exact he t

/-- Every F4 root plane admits a common actual-matrix chart in a standard pair.
The placement, pair routes and signed parameter changes are all constructed;
no finiteness, characteristic restriction or completion-level premise is needed. -/
theorem hasPairPlaneCharts (F : Type*) [Field F] : HasPairPlaneCharts F :=
  hasPairPlaneCharts_of_placement F hasPlanePlacement

/-- Application to the original plane-relation consumer. Route coherence remains
its separate completion-level input; plane placement is purely geometric. -/
theorem rootTransport_planes_of_coherence_and_placement (F : Type*) [Field F]
    (hc : TransportCoherent F) (hplacement : HasPlanePlacement)
    (a b : typeF4Roots) (v : RootPlaneWord F a b)
    (hv : rootPlaneEvaluation F a b v = 1) :
    rootTransport F (rootPlaneInclusion F a b v) = 1 :=
  rootTransport_planes_of_coherence_and_charts F hc
    (hasPairPlaneCharts_of_placement F hplacement) a b v hv

/-- The actual charts discharge the plane-chart obligation in GLS3 §2.9.3.
Only completion-level route coherence remains for the root-transport assembly. -/
theorem rootTransport_planes_of_coherence (F : Type*) [Field F]
    (hc : TransportCoherent F) (a b : typeF4Roots) (v : RootPlaneWord F a b)
    (hv : rootPlaneEvaluation F a b v = 1) :
    rootTransport F (rootPlaneInclusion F a b v) = 1 :=
  rootTransport_planes_of_coherence_and_charts F hc (hasPairPlaneCharts F) a b v hv

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation
