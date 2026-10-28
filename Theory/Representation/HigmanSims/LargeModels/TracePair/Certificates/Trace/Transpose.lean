module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Transpose.Checks
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace.Pairing

/-!
# Certified transpose and packed trace for the degree-896 HS generators

A proved bit-routing network transposes 128-by-128 blocks. Kernel-checked
certificates cover all 49 blocks, on both coefficient planes, of the unchanged
ATLAS generator B and the fixed candidate columns. This establishes the exact
matrix transpose equation without any additional premise. Applying the existing
pairing theorem then gives the separating packed trace omega.

Source: ATLAS HSG1-f4r896aB0.g2, recorded unchanged with its SHA-256 in
`../../source/manifest.json`. The encoding, attribution and measured certificate
construction are described in `Transpose/source/README.md`.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace

/-- The fixed packed columns are precisely the transpose of generator B. -/
theorem columnsB_eval :
    Packed.eval 896 columnsB = (Packed.eval 896 generatorRowsB).transpose :=
  Transpose.eval_eq_transpose generatorRowsB columnsB Transpose.blocks_checked

/-- The transpose certificate discharges the remaining premise of the full
packed pairing calculation, including its final omega parity. -/
theorem trace_packed :
    (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB).trace = omega :=
  trace_packed_of_transpose columnsB_eval

end Representation.HigmanSims.LargeModels.TracePair.Certificates.Trace
