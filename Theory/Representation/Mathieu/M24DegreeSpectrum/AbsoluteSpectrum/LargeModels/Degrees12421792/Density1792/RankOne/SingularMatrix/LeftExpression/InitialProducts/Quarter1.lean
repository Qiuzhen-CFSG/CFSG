module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks13

/-!
# Initial left-product checks on rows 448–895

Seven exact 64-row certificates establish TB and DA on this interval, with
all 1792 columns and the original untransposed ATLAS matrices. The shared
`product_range` lemma joins adjacent slices of the published input and output
lists without evaluating their data again.

These unconditional exports discharge the second-quarter premises of
`LeftCertificate.tb_checked_of_quarters` and
`LeftCertificate.da_checked_of_quarters`, then of
`packedLeft_eq_leftExpression_of_initial_quarters`.
See `source/README.md` and `../source/README.md` for the factorization,
ATLAS attribution and G. D. James's mathematical application.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter1

theorem tb_checked :
    Wide.checkRows 1792 ((tRows.drop 448).take 448) RightCertificate.wideSecond
      ((tbRows.drop 448).take 448) = true := by
  apply product_range tRows RightCertificate.wideSecond tbRows 448 64 384 Block07.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows 512 64 320 Block08.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows 576 64 256 Block09.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows 640 64 192 Block10.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows 704 64 128 Block11.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows 768 64 64 Block12.tb_checked
  exact Block13.tb_checked

theorem da_checked :
    Wide.checkRows 1792 ((dRows.drop 448).take 448) RightCertificate.wideFirst
      ((daRows.drop 448).take 448) = true := by
  apply product_range dRows RightCertificate.wideFirst daRows 448 64 384 Block07.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows 512 64 320 Block08.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows 576 64 256 Block09.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows 640 64 192 Block10.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows 704 64 128 Block11.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows 768 64 64 Block12.da_checked
  exact Block13.da_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter1

