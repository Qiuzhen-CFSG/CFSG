module

public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.Products
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAB
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAbAb
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAb2Ab2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAb4Ab4
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAb8Ab2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAb10Ab
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAbB
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAbbAbb
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAbb2Abb2
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAbb4Abb
public import Theory.Representation.HigmanSims.LargeModels.Restricted1408.Descent.MatrixRelations.SmallWords.AlternatingProducts.ProductAbb5Abb5

/-!
# The eleven alternating products of the literal HS matrices

Complete kernel-checked row certificates prove all products shared by
(AB)¹¹ and (ABB)¹⁰, with the published intermediate tables unchanged.
No inverse, generator relation or interpretation of an intermediate is assumed.
The sound row-to-matrix bridges retain the source multiplication convention.
See `AlternatingProducts/README.md` and `SmallWords/source/README.md`.
-/

public section
namespace Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
open AlternatingCertificate

/-- All eleven literal alternating-word products, without extra premises. -/
theorem alternatingProducts : AlternatingProducts where
  a_b := mul_of_rows aRows bRows abRows b_size a_b_rows
  ab_ab := mul_of_rows abRows abRows ab2Rows ab_size ab_ab_rows
  ab2_ab2 := mul_of_rows ab2Rows ab2Rows ab4Rows ab2_size ab2_ab2_rows
  ab4_ab4 := mul_of_rows ab4Rows ab4Rows ab8Rows ab4_size ab4_ab4_rows
  ab8_ab2 := mul_of_rows ab8Rows ab2Rows ab10Rows ab2_size ab8_ab2_rows
  ab10_ab := mul_one_of_rows ab10Rows abRows ab_size ab10_ab_rows
  ab_b := mul_of_rows abRows bRows abbRows b_size ab_b_rows
  abb_abb := mul_of_rows abbRows abbRows abb2Rows abb_size abb_abb_rows
  abb2_abb2 := mul_of_rows abb2Rows abb2Rows abb4Rows abb2_size abb2_abb2_rows
  abb4_abb := mul_of_rows abb4Rows abbRows abb5Rows abb_size abb4_abb_rows
  abb5_abb5 := mul_one_of_rows abb5Rows abb5Rows abb5_size abb5_abb5_rows

end Representation.HigmanSims.LargeModels.Restricted1408.RelationCertificate.SmallWordProducts
