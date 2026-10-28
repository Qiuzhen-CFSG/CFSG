module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.Spectral
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.EightRoots
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness.InvariantRoots

/-!
# Trace-eight witnesses from invariant E₈ root lattices

Every polynomial fixed-free cubic preserves the span of a concrete scaled
E₈ root configuration, by the short-vector geometry in `InvariantRoots`.
The eight-root construction preserves the full integral Leech lattice and
computes the trace of its unique rational extension. Applying it to that
configuration proves all clauses of `IntegralCubicTraceEight`.

Source context: Aschbacher, *Sporadic Groups* (1994), 25.1–25.5
(pp.132–134), for the octad lattice. The existence proof uses the additional
coordinate argument in the imported modules. Chapter 9 Exercise 6 (p.141)
proves fixed-freeness of the class specified in 25.9, not this converse.
The conjugacy-class recognition of 49.1–49.4 remains independent.
-/

@[expose] public noncomputable section
open Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- Construct the requested integral witness from invariant eight-root lattices. -/
theorem integralCubicTraceEight_of_stableE8Roots
    (hexists : TraceEightWitness.StableE8RootsExist) : IntegralCubicTraceEight := by
  intro r hr hp
  obtain ⟨s, hs⟩ := hexists r hr hp
  exact ⟨s.integralReflection,
    s.traceEight_witness_of_rational_root_action r (hr ▸ pow_orderOf_eq_one r) hs⟩

/-- Every polynomial fixed-free integral Leech cubic centralizes an integral
involution whose unique rational extension has trace eight. -/
theorem integralCubicTraceEight : IntegralCubicTraceEight :=
  integralCubicTraceEight_of_stableE8Roots TraceEightWitness.stableE8RootsExist

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
