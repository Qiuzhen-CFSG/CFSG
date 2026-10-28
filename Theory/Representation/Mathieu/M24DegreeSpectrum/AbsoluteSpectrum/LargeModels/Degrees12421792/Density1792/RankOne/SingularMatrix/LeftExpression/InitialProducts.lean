module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.BlockAssembly
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Quarter0
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Quarter1
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Quarter2
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Quarter3

/-!
# Assembly of the first two left products

Four disjoint 448-row certificates cover each of the fixed TB and DA products,
retaining all 1792 columns of the original untransposed ATLAS matrices.
Structural range composition joins the checked quarters without re-evaluating
their scalar arithmetic. The unconditional exports discharge the first two
product premises of `packedLeft_eq_leftExpression_of_checks`; expansion
validation and the final two products remain separate. The conditional
quarter interfaces are preserved. See InitialProducts/source/README.md for
source attribution and the definitions T = A+B and D = T+TB.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate

private theorem product_of_quarters (a w c : List Nat)
    (ha : a.length = 1792) (hc : c.length = 1792)
    (h0 : Wide.checkRows 1792 ((a.drop 0).take 448) w
      ((c.drop 0).take 448) = true)
    (h1 : Wide.checkRows 1792 ((a.drop 448).take 448) w
      ((c.drop 448).take 448) = true)
    (h2 : Wide.checkRows 1792 ((a.drop 896).take 448) w
      ((c.drop 896).take 448) = true)
    (h3 : Wide.checkRows 1792 ((a.drop 1344).take 448) w
      ((c.drop 1344).take 448) = true)
    : Wide.checkRows 1792 a w c = true := by
  have h := InitialProducts.product_range a w c 0 448 1344 h0
    (InitialProducts.product_range a w c 448 448 896 h1
      (InitialProducts.product_range a w c 896 448 448 h2 h3))
  simpa only [List.drop_zero, List.take_of_length_le (Nat.le_of_eq ha),
    List.take_of_length_le (Nat.le_of_eq hc)] using h

theorem tb_checked_of_quarters
    (h0 : Wide.checkRows 1792 ((tRows.drop 0).take 448)
      RightCertificate.wideSecond ((tbRows.drop 0).take 448) = true)
    (h1 : Wide.checkRows 1792 ((tRows.drop 448).take 448)
      RightCertificate.wideSecond ((tbRows.drop 448).take 448) = true)
    (h2 : Wide.checkRows 1792 ((tRows.drop 896).take 448)
      RightCertificate.wideSecond ((tbRows.drop 896).take 448) = true)
    (h3 : Wide.checkRows 1792 ((tRows.drop 1344).take 448)
      RightCertificate.wideSecond ((tbRows.drop 1344).take 448) = true)
    : Wide.checkRows 1792 tRows RightCertificate.wideSecond tbRows = true := by
  have hA : Data1792.firstRows.toList.length = 1792 := by decide +kernel
  have hB : Data1792.secondRows.toList.length = 1792 := by decide +kernel
  have hT : tRows.length = 1792 := by
    simp only [tRows, List.length_zipWith, hA, hB, Nat.min_self]
  exact product_of_quarters _ _ _ hT (by decide +kernel) h0 h1 h2 h3

theorem da_checked_of_quarters
    (h0 : Wide.checkRows 1792 ((dRows.drop 0).take 448)
      RightCertificate.wideFirst ((daRows.drop 0).take 448) = true)
    (h1 : Wide.checkRows 1792 ((dRows.drop 448).take 448)
      RightCertificate.wideFirst ((daRows.drop 448).take 448) = true)
    (h2 : Wide.checkRows 1792 ((dRows.drop 896).take 448)
      RightCertificate.wideFirst ((daRows.drop 896).take 448) = true)
    (h3 : Wide.checkRows 1792 ((dRows.drop 1344).take 448)
      RightCertificate.wideFirst ((daRows.drop 1344).take 448) = true)
    : Wide.checkRows 1792 dRows RightCertificate.wideFirst daRows = true := by
  have hA : Data1792.firstRows.toList.length = 1792 := by decide +kernel
  have hB : Data1792.secondRows.toList.length = 1792 := by decide +kernel
  have hT : tRows.length = 1792 := by
    simp only [tRows, List.length_zipWith, hA, hB, Nat.min_self]
  have hTB : tbRows.length = 1792 := by decide +kernel
  have hD : dRows.length = 1792 := by
    simp only [dRows, List.length_zipWith, hT, hTB, Nat.min_self]
  exact product_of_quarters _ _ _ hD (by decide +kernel) h0 h1 h2 h3

/-- The full fixed-data check for TB, with every row and column included. -/
theorem tb_checked :
    Wide.checkRows 1792 tRows RightCertificate.wideSecond tbRows = true :=
  tb_checked_of_quarters InitialProducts.Quarter0.tb_checked
    InitialProducts.Quarter1.tb_checked InitialProducts.Quarter2.tb_checked
    InitialProducts.Quarter3.tb_checked

/-- The full fixed-data check for DA, with every row and column included. -/
theorem da_checked :
    Wide.checkRows 1792 dRows RightCertificate.wideFirst daRows = true :=
  da_checked_of_quarters InitialProducts.Quarter0.da_checked
    InitialProducts.Quarter1.da_checked InitialProducts.Quarter2.da_checked
    InitialProducts.Quarter3.da_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate

