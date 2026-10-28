module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks20

/-!
# Initial left products on rows 896 through 1343

Seven adjacent 64-row certificates prove the exact TB and DA checks on this
quarter, retaining all 1792 columns. Each block connects its literal masks to
the published rows for the original untransposed ATLAS matrices, T = A + B
and D = T + TB. Structural range composition avoids re-evaluating the data.

These two unconditional checks supply the third-quarter inputs to
`LeftCertificate.tb_checked_of_quarters` and `da_checked_of_quarters`, then
`packedLeft_eq_leftExpression_of_initial_quarters`. The other quarters and
the separate matrix-interpretation checks belong to their assembly owners.
See source/README.md and ../source/README.md for ATLAS attribution and the
application to James, *The modular characters of the Mathieu groups* (1973).
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter2

theorem tb_checked :
    Wide.checkRows 1792 ((tRows.drop 896).take 448) RightCertificate.wideSecond
      ((tbRows.drop 896).take 448) = true := by
  apply product_range tRows RightCertificate.wideSecond tbRows
    896 64 384 Block14.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    960 64 320 Block15.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    1024 64 256 Block16.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    1088 64 192 Block17.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    1152 64 128 Block18.tb_checked
  apply product_range tRows RightCertificate.wideSecond tbRows
    1216 64 64 Block19.tb_checked
  exact Block20.tb_checked

theorem da_checked :
    Wide.checkRows 1792 ((dRows.drop 896).take 448) RightCertificate.wideFirst
      ((daRows.drop 896).take 448) = true := by
  apply product_range dRows RightCertificate.wideFirst daRows
    896 64 384 Block14.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    960 64 320 Block15.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    1024 64 256 Block16.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    1088 64 192 Block17.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    1152 64 128 Block18.da_checked
  apply product_range dRows RightCertificate.wideFirst daRows
    1216 64 64 Block19.da_checked
  exact Block20.da_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter2
