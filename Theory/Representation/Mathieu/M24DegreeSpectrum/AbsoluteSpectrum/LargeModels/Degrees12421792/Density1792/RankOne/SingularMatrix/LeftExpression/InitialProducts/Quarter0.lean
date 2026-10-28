module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks03
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks04
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks05
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks06

/-!
# Initial left products on rows 0 through 447

Seven adjacent 64-row certificates prove the exact TB and DA checks on the
first quarter, retaining all 1792 columns of the original untransposed ATLAS
matrices. Each block connects its scalar witnesses to the published masks;
`product_range` concatenates these checks without evaluating the data again.
See source/README.md for ATLAS attribution and the definitions T = A+B and
D = T+TB. These exports discharge the first-quarter premises of
`LeftCertificate.tb_checked_of_quarters` and `da_checked_of_quarters`, hence
of `packedLeft_eq_leftExpression_of_initial_quarters`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter0

theorem tb_checked :
    Wide.checkRows 1792 ((tRows.drop 0).take 448)
      RightCertificate.wideSecond ((tbRows.drop 0).take 448) = true := by
  apply product_range tRows RightCertificate.wideSecond tbRows
    0 64 384 Block00.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    64 64 320 Block01.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    128 64 256 Block02.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    192 64 192 Block03.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    256 64 128 Block04.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    320 64 64 Block05.tb_checked
  exact Block06.tb_checked

theorem da_checked :
    Wide.checkRows 1792 ((dRows.drop 0).take 448)
      RightCertificate.wideFirst ((daRows.drop 0).take 448) = true := by
  apply product_range dRows RightCertificate.wideFirst daRows
    0 64 384 Block00.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    64 64 320 Block01.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    128 64 256 Block02.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    192 64 192 Block03.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    256 64 128 Block04.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    320 64 64 Block05.da_checked
  exact Block06.da_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter0
