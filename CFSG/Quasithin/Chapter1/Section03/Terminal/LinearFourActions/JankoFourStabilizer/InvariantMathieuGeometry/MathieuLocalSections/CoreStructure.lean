module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.MathieuLocalSections.Reduction
public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# Intrinsic structure of the native M₂₄ octad stabilizers

The native octad action has elementary pointwise kernel and alternating
image. A fixed-point-free heptad three-cycle puts the kernel in the derived
subgroup, proving perfectness; simplicity of the alternating image puts
the intrinsic two-core inside that elementary kernel.

This discharges the octad structure contract used by the local L₄(2)
section assembly. Placement of arbitrary source-local subgroups remains
with that assembly's separate geometric argument.

Source: GLS3, Table 5.3e, E₁₆.A₈; Aschbacher--Smith, A.3.12(14),
combined manuscript of 1 March 2004, printed pp.47--48.
-/

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections

/-- Every native M₂₄ octad stabilizer is perfect, with elementary abelian intrinsic two-core. -/
public theorem octadCoreStructure : OctadCoreStructure :=
  Sporadic.Mathieu.M24LocalGeometry.LinearFourCore.octad_core_structure

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections
