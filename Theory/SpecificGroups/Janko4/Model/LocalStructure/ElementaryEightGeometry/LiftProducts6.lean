module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.LiftProducts5

/-!
# Checked products for the native lift words

Each packed equality is checked by Lean and denotes ordinary binary matrix
multiplication. Sequential batches bound simultaneous certificate memory.
-/

public section
namespace Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
open Janko4.GeneratorCertificates Janko4.Cardinality.KernelCount
set_option maxRecDepth 10000
set_option Elab.async false
set_option maxHeartbeats 800000 in
theorem product_w147 : packedMul w146Rows w61Rows = w147Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w148 : packedMul w147Rows inverseYRows = w148Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w149 : packedMul w148Rows w11Rows = w149Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w150 : packedMul w149Rows w49Rows = w150Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w151 : packedMul w150Rows yRows = w151Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w152 : packedMul w151Rows w16Rows = w152Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w153 : packedMul w152Rows w20Rows = w153Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w154 : packedMul w153Rows w35Rows = w154Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w155 : packedMul w154Rows w13Rows = w155Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w156 : packedMul w155Rows w10Rows = w156Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w157 : packedMul w156Rows w13Rows = w157Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w158 : packedMul yRows w62Rows = w158Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w159 : packedMul w158Rows inverseYRows = w159Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w160 : packedMul w159Rows w43Rows = w160Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w161 : packedMul w160Rows w8Rows = w161Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w162 : packedMul w161Rows w63Rows = w162Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w163 : packedMul w162Rows w11Rows = w163Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w164 : packedMul w163Rows w7Rows = w164Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w165 : packedMul w164Rows xRows = w165Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w166 : packedMul w165Rows w36Rows = w166Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w167 : packedMul w166Rows w46Rows = w167Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w168 : packedMul w167Rows w42Rows = w168Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w169 : packedMul w168Rows w31Rows = w169Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
set_option maxHeartbeats 800000 in
theorem product_w170 : packedMul w169Rows w44Rows = w170Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryEightGeometry.LiftMatrices
