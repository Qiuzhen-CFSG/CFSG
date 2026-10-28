module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.Rows

/-! Kernel-checked wordproducts certificates. See `Conjugacy.Rows` for attribution. -/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem word0110101101011 : packedMul conj011010Rows conj1101011Rows = conj0110101101011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word0110111011110 : packedMul conj011011Rows conj1011110Rows = conj0110111011110Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word0111010110101 : packedMul conj011101Rows conj0110101Rows = conj0111010110101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word1110101101010 : packedMul conj111010Rows conj1101010Rows = conj1110101101010Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word01110101101010 : packedMul conj0111010Rows conj1101010Rows = conj01110101101010Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word110101011101011 : packedMul conj1101010Rows conj11101011Rows = conj110101011101011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word111010111010101 : packedMul conj1110101Rows conj11010101Rows = conj111010111010101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
