module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Rows

/-!
# Checked native fusion products

Each certificate is kernel-checked and denotes ordinary matrix multiplication.
The import chain bounds simultaneous certificate elaboration.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
open Janko4.GeneratorCertificates Janko4.Cardinality.KernelCount
open Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem product_f4 : packedMul inverseYRows xRows = f4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
