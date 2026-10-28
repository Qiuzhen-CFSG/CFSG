module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Fusion.Products1

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
theorem product_f25 : packedMul f24Rows f18Rows = f25Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f26 : packedMul f25Rows f15Rows = f26Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f27 : packedMul f26Rows f5Rows = f27Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f28 : packedMul f27Rows f11Rows = f28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f29 : packedMul f28Rows f11Rows = f29Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f30 : packedMul f29Rows f9Rows = f30Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f31 : packedMul f30Rows f11Rows = f31Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f32 : packedMul f31Rows f5Rows = f32Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f33 : packedMul f32Rows f8Rows = f33Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f34 : packedMul f33Rows f8Rows = f34Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f35 : packedMul f34Rows f19Rows = f35Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f36 : packedMul f35Rows f16Rows = f36Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f37 : packedMul f36Rows f10Rows = f37Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f38 : packedMul f37Rows f12Rows = f38Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f39 : packedMul f38Rows f4Rows = f39Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f40 : packedMul f39Rows yRows = f40Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f41 : packedMul f40Rows f20Rows = f41Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f42 : packedMul f41Rows f9Rows = f42Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f43 : packedMul f42Rows f14Rows = f43Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_f44 : packedMul f43Rows f9Rows = f44Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.FusionMatrices
