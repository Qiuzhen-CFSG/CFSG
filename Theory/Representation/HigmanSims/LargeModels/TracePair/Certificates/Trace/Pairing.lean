module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.PairingData

/-!
# Kernel-checked packed pairing for the degree-896 HS trace

The 28 bounded products, their concatenations with the fixed source data, their
XOR sum and its parity are all checked in the kernel. The remaining hypothesis
is that the separately supplied candidate columns really transpose the second
shared generator. No density, descent or character-theoretic premise is used.

See `source/README.md` for the source and computation measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace

private theorem chunks_checked : checkChunks pairingChunks = true := by decide +kernel

private theorem chunks_left : pairingChunks.flatMap PairChunk.left = generatorRowsA := by
  decide +kernel

private theorem chunks_right : pairingChunks.flatMap PairChunk.right = columnsB := by
  decide +kernel

private theorem values_checked : sumValues pairingChunks = pairingValue := by decide +kernel

theorem productsSum_generators_columns : productsSum generatorRowsA columnsB = pairingValue := by
  rw [← chunks_left, ← chunks_right, productsSum_chunks pairingChunks chunks_checked, values_checked]

/-- The full coefficientwise pairing has parity omega. The transposition of the
candidate columns is an independent obligation. -/
theorem pairing_parity :
    Packed.decode (sumRow 896 (productsSum generatorRowsA columnsB)) 0 = omega := by
  rw [productsSum_generators_columns]
  decide +kernel

theorem trace_packed_of_transpose
    (ht : Packed.eval 896 columnsB = (Packed.eval 896 generatorRowsB).transpose) :
    (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB).trace = omega := by
  rw [trace_eq_of_transpose 896 generatorRowsA generatorRowsB columnsB
    generatorRowsA_length columnsB_length ht]
  exact pairing_parity

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace
