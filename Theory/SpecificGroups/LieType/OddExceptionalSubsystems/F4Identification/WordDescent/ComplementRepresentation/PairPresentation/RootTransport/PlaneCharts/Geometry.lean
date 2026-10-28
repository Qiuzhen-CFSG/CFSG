module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairPresentation.RootTransport

/-!
# The remaining geometric input for F4 plane charts

`HasPlanePlacement` asks only for a Weyl word moving two spanning roots into
one standard pair's real span. Linearity then moves every root of the original
plane into that same span. Combined with `PairRoutes` and `MatrixTransport`,
this gives the actual matrix charts, including intermediate and opposite roots.
The existence of such a placement is not asserted in this module.

Source: GLS3 §2.9.3, `refs/KGroup/GLS3/chapter2.tex`, lines 1455–1462.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open scoped Classical
attribute [local instance] Classical.decEq
local instance planeChartsGeometryRootFintype : Fintype typeF4Roots := Fintype.ofFinite _

/-- The root-system part of plane placement: one Weyl word sends the two
spanning roots into the real span of one standard pair. -/
def HasPlanePlacement : Prop :=
  ∀ a b : typeF4Roots, ∃ (w : List typeF4RootPairing_base.support) (i j : Fin 4),
    reflectionWord (P := typeF4RootPairing) w a ∈
        rootPlane (signedRoot true i) (signedRoot true j) ∧
      reflectionWord (P := typeF4RootPairing) w b ∈
        rootPlane (signedRoot true i) (signedRoot true j)

/-- Membership of the spanning roots controls every root in the plane, with
no exclusion of intermediate roots or rank-one spans. -/
theorem plane_image_mem_of_generators
    (w : List typeF4RootPairing_base.support) (a b c d : typeF4Roots)
    (ha : reflectionWord (P := typeF4RootPairing) w a ∈ rootPlane c d)
    (hb : reflectionWord (P := typeF4RootPairing) w b ∈ rootPlane c d)
    (r : rootPlane a b) :
    reflectionWord (P := typeF4RootPairing) w r.val ∈ rootPlane c d := by
  obtain ⟨x, y, hr⟩ := Submodule.mem_span_pair.mp r.property
  have hlinear (q : typeF4Roots) :
      typeF4RootPairing.root (reflectionWord w q) =
        (typeF4RootPairing_base.wordProd w).val.weightMap (typeF4RootPairing.root q) := by
    rw [root_reflectionWord]
    rfl
  change typeF4RootPairing.root (reflectionWord w a) ∈
    Submodule.span ℝ {typeF4RootPairing.root c, typeF4RootPairing.root d} at ha
  change typeF4RootPairing.root (reflectionWord w b) ∈
    Submodule.span ℝ {typeF4RootPairing.root c, typeF4RootPairing.root d} at hb
  rw [hlinear] at ha hb
  change typeF4RootPairing.root (reflectionWord w r.val) ∈
    Submodule.span ℝ {typeF4RootPairing.root c, typeF4RootPairing.root d}
  rw [hlinear, ← hr, map_add, map_smul, map_smul]
  exact (Submodule.span ℝ {typeF4RootPairing.root c, typeF4RootPairing.root d}).add_mem
    ((Submodule.span ℝ _).smul_mem x ha) ((Submodule.span ℝ _).smul_mem y hb)

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.PlaneCharts
