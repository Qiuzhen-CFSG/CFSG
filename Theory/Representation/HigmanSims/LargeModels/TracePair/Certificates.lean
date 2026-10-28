module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.DensityCriterion
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.PackedGenerators
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Reencoding
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Projector
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.OrbitSpans
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace

/-!
# Finite certificates for the degree-896 HS matrices

The literal ATLAS HSG1-f4r896aB0 matrices generate the full matrix algebra,
and their product has trace omega. The density proof combines a normalized
null pair for A + B + omega² I, a checked inverse of its rank-one perturbation,
and two spanning orbits. The trace proof uses the checked packed pairing with
the transpose of B. The generator re-encoding theorems discharge every
interpretation premise in these independent finite certificates.

For every actual marked action, these results give absolute irreducibility
and trace omega at the literal carrier element AB. Existence of that action
is the separate carrier-descent obligation. Source downloads, conventions and
certificate provenance are recorded in `source/` and `Certificates/source/`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair
open Certificates

/-- The literal degree-896 ATLAS generators span the full matrix algebra. -/
theorem matrixAlgebraFull : MatrixAlgebraFull :=
  full_of_nullProjector
    (nullProjector_mem_of_reencoding generatorRowsA_eval generatorRowsB_eval)
    (columnOrbitSpan_eq_top_of_reencoding generatorRowsA_eval generatorRowsB_eval)
    (rowOrbitSpan_eq_top_of_reencoding generatorRowsA_eval generatorRowsB_eval)

/-- The product of the literal degree-896 ATLAS generators has trace omega. -/
theorem trace_matrixA_mul_matrixB : (matrixA * matrixB).trace = omega :=
  trace_matrixA_mul_matrixB_of_reencoding generatorRowsA_eval generatorRowsB_eval

/-- The finite certificates discharge the density premise for every actual
action with the published generator marking. -/
theorem MarkedAction.absolutelyIrreducible_of_certificates (M : MarkedAction) :
    M.rep.IsAbsolutelyIrreducible :=
  M.absolutelyIrreducible matrixAlgebraFull

/-- The separating trace at the literal carrier element AB. -/
theorem MarkedAction.trace_eq_omega (M : MarkedAction) :
    LinearMap.trace Four _ (M.rep traceElement) = omega := by
  rw [M.trace_product]
  exact trace_matrixA_mul_matrixB

/-- Application of the density criterion to the literal carrier marking,
retained for callers supplying their own finite certificates. -/
theorem MarkedAction.absolutelyIrreducible_of_finite_checks (M : MarkedAction)
    (T : Matrix (Fin 896) (Fin 896) Four)
    (hu : singular.mulVec nullColumn = 0)
    (hv : Matrix.vecMul nullRow singular = 0)
    (hT : (singular + Matrix.vecMulVec nullColumn nullRow) * T = 1)
    (hc : columnOrbitSpan = ⊤) (hr : rowOrbitSpan = ⊤) :
    M.rep.IsAbsolutelyIrreducible :=
  M.absolutelyIrreducible (full_of_finite_checks T hu hv hT hc hr)

end Representation.HigmanSims.LargeModels.TracePair
