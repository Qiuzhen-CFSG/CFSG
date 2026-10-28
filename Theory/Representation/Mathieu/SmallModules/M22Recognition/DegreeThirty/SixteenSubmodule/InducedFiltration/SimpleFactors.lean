module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateInterface
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors.F0
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors.F2
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors.F4
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.SimpleFactors.F7

/-!
# Binary simplicity of the eight saved adjoint factors

The four one-dimensional factors are automatic. The two 34-dimensional
factors have checked rank-one algebra elements with spanning row and column
orbits. The two 140-dimensional factors use rank-two elements: a spanning
dual orbit detects a nonzero image in every nonzero invariant subspace,
and each of the three nonzero binary image vectors has a spanning orbit.
Every finite identity is checked against the literal saved matrix blocks.

This discharges the simplicity input of `binary_factorDegreeFiltration_of_certificates`.
The independent native flag comparison remains explicit in the application.
Source context: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, printed pp.451--452 and 457.
-/

public section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration

/-- Every displayed binary factor of the saved adapted action is simple. -/
theorem factorSimple : ∀ t : Factor, FactorSimple t := by
  intro t
  fin_cases t
  · exact SimpleFactors.F0.simple
  · exact small_factors_simple.1
  · exact SimpleFactors.F2.simple
  · exact small_factors_simple.2.1
  · exact SimpleFactors.F4.simple
  · exact small_factors_simple.2.2.1
  · exact small_factors_simple.2.2.2
  · exact SimpleFactors.F7.simple

/-- The checked simplicity certificates leave only the native flag comparison
for the actual induced binary adjoint filtration. -/
theorem binary_factorDegreeFiltration_of_flagCoordinates (C : FlagCoordinates) :
    FactorDegreeFiltration {d : ℕ | d ≤ 10 ∨ 30 < d} GeneratorMatrices.binaryAdjoint :=
  binary_factorDegreeFiltration_of_certificates C factorSimple

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
