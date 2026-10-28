module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Products
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.GeneratorProducts.Rows

/-!
# The four exact generator products for the degree-1408 HS matrices

Kernel-checked packed-row certificates prove A² = 1, B² = b2, b2² = I,
and IB = 1 on all 1408 coordinates. The decoder bridges identify these
with ordinary products of the unchanged matrices. No inverse or relator
identity is assumed. This supplies `GeneratorProducts` to the existing
`smallWords_of_products`, discharging the first two clauses of the retained
ATLAS HSG1-P1.M. See `GeneratorProducts/source/README.md` for the method,
source attribution, and measured verification cost.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
open GeneratorCertificate

/-- Unconditional certificates for A² and the three products giving B⁵. -/
theorem generatorProducts : GeneratorProducts where
  a_a := mul_one_of_rows aRows aRows (by decide +kernel) a_a_rows
  b_b := mul_of_rows bRows bRows b2Rows (by decide +kernel) b_b_rows
  b2_b2 := mul_of_rows b2Rows b2Rows inverseRows (by decide +kernel) b2_b2_rows
  inverse_b := mul_one_of_rows inverseRows bRows (by decide +kernel) inverse_b_rows

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
