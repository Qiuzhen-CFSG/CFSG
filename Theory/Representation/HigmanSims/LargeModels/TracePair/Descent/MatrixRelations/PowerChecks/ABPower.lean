module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Assembly
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.BasisC
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Squares
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Fifth
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower.Closing

/-!
# Certificates for the eleventh power of the exact HS product

`ABProduct.ab_eq_c` proves that the candidate C is the literal packed product
AB in the original order. `BasisC` supplies all coordinate-row images for C.
`Squares`, `Fifth`, and `Closing` certify all five remaining numerical products
along the addition chain 1, 2, 4, 5, 10, 11. Applying
`pow_eleven_eq_one_of_products` gives the unconditional identity `(AB)^11 = 1`
over the unchanged `Four`, without assuming an HS action or invertibility.

Source: relator 2 of the unchanged `Descent/source/HSG1-P1.M`; the original
ATLAS matrices and coefficient convention are documented in `TracePair/source/`.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower
open Certificates

/-- Relator 2 of the retained source presentation for the literal packed matrices. -/
theorem pow_eleven_eq_one :
    (Packed.eval 896 generatorRowsA * Packed.eval 896 generatorRowsB) ^ 11 = 1 :=
  pow_eleven_eq_one_of_products
    Squares.c_square_eq_d Squares.d_square_eq_e Fifth.c_mul_e_eq_f
    Closing.f_square_eq_g Closing.g_mul_c_eq_one

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABPower
