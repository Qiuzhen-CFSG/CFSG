module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.Rows

/-! Kernel-checked fusionproducts certificates. See `Conjugacy.Rows` for attribution. -/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem fusion012_left : packedMul uRows conj1110110111110110Rows = fusion012Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion012_right : packedMul conj1110110111110110Rows normal012Rows = fusion012Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion020_left : packedMul uRows conj110101011101011Rows = fusion020Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion020_right : packedMul conj110101011101011Rows normal020Rows = fusion020Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion021_left : packedMul uRows conj1110101110101010Rows = fusion021Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion021_right : packedMul conj1110101110101010Rows normal021Rows = fusion021Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
