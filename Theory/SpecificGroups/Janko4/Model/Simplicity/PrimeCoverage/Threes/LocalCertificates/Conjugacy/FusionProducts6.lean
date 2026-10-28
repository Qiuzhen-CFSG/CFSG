module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Conjugacy.Rows

/-! Kernel-checked fusionproducts certificates. See `Conjugacy.Rows` for attribution. -/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem fusion210_left : packedMul uRows conj111010110101Rows = fusion210Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion210_right : packedMul conj111010110101Rows normal210Rows = fusion210Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion211_left : packedMul uRows conj01110101101010Rows = fusion211Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion211_right : packedMul conj01110101101010Rows normal211Rows = fusion211Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion212_left : packedMul uRows conj0110101101011Rows = fusion212Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
theorem fusion212_right : packedMul conj0110101101011Rows normal212Rows = fusion212Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates.Conjugacy
