module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower.AB
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower.X
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower.X2
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower.X4
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower.X5
public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower.Identity

/-!
# The tenth power of the literal HS word AB²

Six complete row-image certificates establish AB, X = (AB)B, X², X⁴,
X⁵ and (X⁵)² = I. Associativity and the laws of powers identify this with
relator 3 of the unchanged ATLAS `Descent/source/HSG1-P1.M`, in its original
word order over `Four`. No invertibility, representation or other relator
is assumed. See `ABBPower/source/README.md` for certificate generation,
source attribution and compilation measurements.
-/

@[expose] public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower
open Certificates

/-- Source relator 3 holds on the exact packed degree-896 generators. -/
theorem pow_ten_eq_one :
    (Packed.eval 896 generatorRowsA * (Packed.eval 896 generatorRowsB) ^ 2) ^ 10 = 1 := by
  have hx : Packed.eval 896 generatorRowsA * (Packed.eval 896 generatorRowsB) ^ 2 =
      Packed.eval 896 Data.rowsX := by
    rw [pow_two, ← mul_assoc, AB.product_eq, X.product_eq]
  have h2 : (Packed.eval 896 Data.rowsX) ^ 2 = Packed.eval 896 Data.rowsX2 := by
    simpa only [pow_two] using X2.product_eq
  have h4 : (Packed.eval 896 Data.rowsX) ^ 4 = Packed.eval 896 Data.rowsX4 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, h2, pow_two, X4.product_eq]
  have h5 : (Packed.eval 896 Data.rowsX) ^ 5 = Packed.eval 896 Data.rowsX5 := by
    rw [show 5 = 4 + 1 from rfl, pow_succ, h4, X5.product_eq]
  rw [hx, show 10 = 5 * 2 from rfl, pow_mul, h5, pow_two, Identity.product_eq]

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.PowerChecks.ABBPower
