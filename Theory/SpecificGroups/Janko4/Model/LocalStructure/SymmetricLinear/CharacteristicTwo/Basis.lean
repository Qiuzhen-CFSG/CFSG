module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.CharacteristicTwo.Data

/-!+# The certified max4 change of basis

The packed product is checked by the kernel and transported to binary
matrices by `decode_packedMul`. For square matrices a right inverse is also
a left inverse, so only one numerical product needs checking.

The basis was found from the literal ATLAS generators; its provenance is
retained in `CharacteristicTwo/source/README.md`. This calculation certifies
invertibility, without assuming the proposed flag or local group structure.
-/

public section

namespace Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
open GeneratorCertificates Coordinates

set_option maxRecDepth 10000 in
private theorem packed_basis_inverse : packedMul basisRows basisInverseRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

/-- The supplied binary basis and its supplied inverse multiply to one. -/
theorem basis_mul_basisInverse : decodeRows basisRows * decodeRows basisInverseRows = 1 := by
  rw [← decode_packedMul, packed_basis_inverse, decode_packedOne]

/-- The same supplied inverse is a left inverse. -/
theorem basisInverse_mul_basis : decodeRows basisInverseRows * decodeRows basisRows = 1 :=
  (mul_eq_one_comm (a := decodeRows basisRows) (b := decodeRows basisInverseRows)).mp
    basis_mul_basisInverse

end Janko4.LocalStructure.SymmetricLinear.CharacteristicTwo
