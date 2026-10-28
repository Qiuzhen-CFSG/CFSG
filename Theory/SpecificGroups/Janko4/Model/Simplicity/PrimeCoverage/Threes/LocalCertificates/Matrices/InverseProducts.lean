module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.LocalCertificates.Matrices.Rows

/-!
# Kernel products for the commutator and the inverses of its generators

Every multiplication (including a right inverse certificate for each inverse)
is checked row by row with `decide +kernel`. See `Rows` for the source attribution.
-/

public section
namespace Janko4.Simplicity.ThreeLocalCertificates
open Janko4.GeneratorCertificates

set_option maxRecDepth 10000 in
theorem product_uInv : packedMul uRows uInvRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_vInv : packedMul vRows vInvRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_invUV : packedMul uInvRows vInvRows = invUVRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_commLeft : packedMul invUVRows uRows = commLeftRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

set_option maxRecDepth 10000 in
theorem product_z : packedMul commLeftRows vRows = zRows :=
  packedMul_eq_of_rows _ _ _ (by
    decide +kernel)

end Janko4.Simplicity.ThreeLocalCertificates
