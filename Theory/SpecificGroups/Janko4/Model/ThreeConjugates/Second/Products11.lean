module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Second.Products10

/-!
# Matrix witnesses for the second J₄ involution triple

Untrusted row data for words in `r`, `a*r*a⁻¹`, `b*r*b⁻¹`, where
`r = (a*b*a*b*b)^5`. The product certificates check every multiplication
in the kernel. The invertible matrix T intertwines the original generators
with two such words; no ATLAS generation test is trusted by the proof.

Source matrices: ATLAS J4G1-f2r112B0, as attributed in `Model.Data`.
The word search used the ATLAS J4G1-find1 recipe (Wilson–Nickerson–Bray);
see `source/README.md` for the reproducible witness and proof method.
-/

public section
namespace Janko4.ThreeConjugates.SecondCertificate
open GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_standardB : packedMul vuRows viRows = standardBRows :=
  checkProduct_sound (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_t_ti : packedMul tRows tiRows = packedOne :=
  checkIdentity_sound (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_ti_t : packedMul tiRows tRows = packedOne :=
  checkIdentity_sound (by decide +kernel)

set_option maxRecDepth 10000 in
theorem product_a_t : packedMul aRows tRows = a_tRows :=
  checkProduct_sound (by decide +kernel)
end Janko4.ThreeConjugates.SecondCertificate
