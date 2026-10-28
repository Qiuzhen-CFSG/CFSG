module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.Rows

/-! Kernel-checked wordproducts certificates. See `Conjugacy.Rows` for attribution. -/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem word011011 : packedMul conj011Rows conj011Rows = conj011011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word011101 : packedMul conj011Rows conj101Rows = conj011101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word011110 : packedMul conj011Rows conj110Rows = conj011110Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word101011 : packedMul conj101Rows conj011Rows = conj101011Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word101111 : packedMul conj101Rows conj111Rows = conj101111Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word110101 : packedMul conj110Rows conj101Rows = conj110101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem word110111 : packedMul conj110Rows conj111Rows = conj110111Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
