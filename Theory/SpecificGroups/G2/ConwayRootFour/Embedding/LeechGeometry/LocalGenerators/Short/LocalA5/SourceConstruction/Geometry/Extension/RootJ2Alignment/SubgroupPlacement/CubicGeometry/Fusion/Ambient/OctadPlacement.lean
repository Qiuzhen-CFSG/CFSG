module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.Preparation
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.Spectral
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightWitness
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadPlacement.TraceEightRecognition

/-!
# Octad placement from intrinsic involution geometry

Conjugate a commuting integral trace-eight involution to the literal marked
Golay sign, then project that same Leech isometry to the central quotient.
The spectral module proves that quotient commutation for a cubic lifts
without sign ambiguity, and computes the trace of the marked sign.
The converse below also proves that the intrinsic witness condition is
necessary for placement.

The imported existence proof constructs an invariant scaled E₈ root lattice
and its integral sign involution. The independent recognition proof conjugates
every trace-eight involution to the marked octad sign. Combining them proves
`IntegralOctadPlacement` without additional premises. The final application
uses the polynomial lift from Preparation to prove binary `OctadPlacement`.
The conditional reductions remain available.

Source: Aschbacher, *Sporadic Groups* (1994), 25.9, Chapter 9 Exercise 6
(p.141), and 49.3–49.4 (pp.280–282). Fixed-freeness of the specified source
representative alone does not supply this converse placement.
-/

@[expose] public noncomputable section
open Atlas.Conway Atlas.Codes Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion

/-- The two independent geometric inputs imply the literal octad-placement contract. -/
theorem integralOctadPlacement_of_traceEight
    (hrecognition : TraceEightInvolutionRecognition)
    (hwitness : IntegralCubicTraceEight) : IntegralOctadPlacement := by
  intro r hr hp
  obtain ⟨t, ht, hrt⟩ := hwitness r hr hp
  obtain ⟨h, hh⟩ := hrecognition t ht
  apply (octad_conjugator_iff_integral (hr ▸ pow_orderOf_eq_one r)).mpr
  exact ⟨h, hh ▸ hrt.map (MulAut.conj h)⟩

/-- The trace-eight witness condition is necessary for the requested placement. -/
theorem integralCubicTraceEight_of_placement (hplacement : IntegralOctadPlacement) :
    IntegralCubicTraceEight := by
  intro r hr hp
  obtain ⟨h, hh⟩ := (octad_conjugator_iff_integral (hr ▸ pow_orderOf_eq_one r)).mp
    (hplacement r hr hp)
  refine ⟨MulAut.conj h⁻¹ integralOctadSign, ⟨?_, ?_⟩, ?_⟩
  · rw [← map_pow, integralOctadSign_sq, map_one]
  · rw [rationalLeechTrace_conj, integralOctadSign_trace]
  · simpa [MulAut.conj_apply, mul_assoc] using hh.map (MulAut.conj h⁻¹)

/-- Feed the binary fixed-free consumer through its genuine order-three lift. -/
theorem octadPlacement_of_traceEight
    (hrecognition : TraceEightInvolutionRecognition)
    (hwitness : IntegralCubicTraceEight) : OctadPlacement :=
  octadPlacement_of_integral (integralOctadPlacement_of_traceEight hrecognition hwitness)

/-- Once recognition is established, the intrinsic witness is exactly the
remaining existence problem, rather than a stronger sufficient assumption. -/
theorem integralOctadPlacement_iff_traceEight
    (hrecognition : TraceEightInvolutionRecognition) :
    IntegralOctadPlacement ↔ IntegralCubicTraceEight :=
  ⟨integralCubicTraceEight_of_placement, integralOctadPlacement_of_traceEight hrecognition⟩

/-- Every polynomial fixed-free integral Leech cubic has a conjugate commuting
with the literal marked octad in the Leech central quotient. -/
theorem integralOctadPlacement : IntegralOctadPlacement :=
  integralOctadPlacement_of_traceEight
    traceEightInvolutionRecognition integralCubicTraceEight

/-- Discharge the geometric placement premise for the ambient-fusion consumer
on the actual binary Leech representation and central quotient. -/
theorem octadPlacement : OctadPlacement :=
  octadPlacement_of_integral integralOctadPlacement

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion
