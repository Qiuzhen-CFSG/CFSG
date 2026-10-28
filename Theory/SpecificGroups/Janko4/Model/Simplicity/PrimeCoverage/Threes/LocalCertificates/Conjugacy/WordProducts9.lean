module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.Rows

/-! Kernel-checked wordproducts certificates. See `Conjugacy.Rows` for attribution. -/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem word111011011111011 : packedMul conj1110110Rows conj11111011Rows = conj111011011111011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word111011111011011 : packedMul conj1110111Rows conj11011011Rows = conj111011111011011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word1110101110101010 : packedMul conj11101011Rows conj10101010Rows = conj1110101110101010Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word1110110111110110 : packedMul conj11101101Rows conj11110110Rows = conj1110110111110110Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
