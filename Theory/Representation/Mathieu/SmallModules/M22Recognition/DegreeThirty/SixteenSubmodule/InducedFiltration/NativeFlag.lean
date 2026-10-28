module

public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.CertificateInterface
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.MatrixChecks
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.NativeFlag.NativeCoordinates
public import Theory.Representation.Mathieu.SmallModules.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration.NativeFlag.Construction

/-!
# The eight-step flag in the native induced binary adjoint

The canonical flattening of the 22-by-16 coordinates intertwines the native
M22 generators with the saved matrices, as proved by the local correction
and packed-column certificates. Composing it with the checked adapted basis
makes all initial coordinate spaces invariant. Block projections identify
their literal successive quotients and both exact diagonal generator actions.

This constructs the unconditional `FlagCoordinates` witness with cumulative
dimensions `0,140,141,175,176,210,211,212,352`. The independent simplicity
certificates are still required by the factor-degree-filtration assembly.

Source: Guralnick--Malle I, Proposition 5.1, pp.15--16;
Aschbacher--Smith, Chapter K, printed pp.451--452 and 457.
-/

@[expose] public noncomputable section
namespace Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration

/-- The saved eight-step flag, realized in the actual native representation
with coordinates on its literal successive quotients. -/
def nativeFlag : FlagCoordinates :=
  NativeFlag.flagCoordinates (NativeFlag.e0.trans MatrixChecks.basisCoordinates)
    (fun k v => by
      change MatrixChecks.basisCoordinates
        (NativeFlag.e0 (GeneratorMatrices.binaryAdjoint (GeneratorMatrices.generator k) v)) = _
      rw [NativeFlag.e0_generator, MatrixChecks.basisCoordinates_generator]
      rfl)
    MatrixChecks.upper

end Representation.MathieuSmall.M22Recognition.DegreeThirty.SixteenSubmodule.InducedFiltration
