module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Marked

/-!
# Separating HS trace from the packed pairing certificate

The full coefficient pairing and its parity are kernel-checked in `Trace.Pairing`.
The block certificates in `Trace.Transpose` identify the fixed candidate columns
with the transpose of the second packed generator. Together they prove the
separating trace, retaining only the two generator re-encoding premises supplied
independently by `Certificates.Reencoding`.

The application uses the literal carrier element `generatorAElement *
generatorBElement`, through `MarkedAction.trace_product`, preserving the source
marking and multiplication conventions. Source: ATLAS HSG1-f4r896aB0;
see `Trace/source/README.md` and `../source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair

/-- Assembly with an explicit transpose equation, retained for callers that
supply that equation directly. -/
theorem trace_matrixA_mul_matrixB_of_reencoding_of_transpose
    (hA : Certificates.Packed.eval 896 Certificates.generatorRowsA = matrixA)
    (hB : Certificates.Packed.eval 896 Certificates.generatorRowsB = matrixB)
    (ht : Certificates.Packed.eval 896 Certificates.Trace.columnsB =
      (Certificates.Packed.eval 896 Certificates.generatorRowsB).transpose) :
    (matrixA * matrixB).trace = omega := by
  rw [← hA, ← hB]
  exact Certificates.Trace.trace_packed_of_transpose ht

/-- The explicit-transpose assembly applied to an actual action with the
source marking. -/
theorem MarkedAction.trace_eq_omega_of_reencoding_of_transpose (M : MarkedAction)
    (hA : Certificates.Packed.eval 896 Certificates.generatorRowsA = matrixA)
    (hB : Certificates.Packed.eval 896 Certificates.generatorRowsB = matrixB)
    (ht : Certificates.Packed.eval 896 Certificates.Trace.columnsB =
      (Certificates.Packed.eval 896 Certificates.generatorRowsB).transpose) :
    LinearMap.trace Four _ (M.rep traceElement) = omega := by
  rw [M.trace_product]
  exact trace_matrixA_mul_matrixB_of_reencoding_of_transpose hA hB ht

/-- The certified transpose and pairing give the separating trace of the
literal matrices, using only their shared generator re-encoding equations. -/
theorem trace_matrixA_mul_matrixB_of_reencoding
    (hA : Certificates.Packed.eval 896 Certificates.generatorRowsA = matrixA)
    (hB : Certificates.Packed.eval 896 Certificates.generatorRowsB = matrixB) :
    (matrixA * matrixB).trace = omega :=
  trace_matrixA_mul_matrixB_of_reencoding_of_transpose hA hB Certificates.Trace.columnsB_eval

/-- At the actual carrier element AB, every action with the source marking has
trace omega. Only the two independent generator re-encodings remain explicit. -/
theorem MarkedAction.trace_eq_omega_of_reencoding (M : MarkedAction)
    (hA : Certificates.Packed.eval 896 Certificates.generatorRowsA = matrixA)
    (hB : Certificates.Packed.eval 896 Certificates.generatorRowsB = matrixB) :
    LinearMap.trace Four _ (M.rep traceElement) = omega := by
  rw [M.trace_product]
  exact trace_matrixA_mul_matrixB_of_reencoding hA hB

end Representation.HigmanSims.LargeModels.TracePair
