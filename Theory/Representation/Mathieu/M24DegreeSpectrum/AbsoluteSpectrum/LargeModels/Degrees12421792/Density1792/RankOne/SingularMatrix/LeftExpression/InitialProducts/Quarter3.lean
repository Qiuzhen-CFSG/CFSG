module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.BlockAssembly
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks21
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks22
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks25
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks26
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Checks27

/-!
# Initial left products on rows 1344 through 1791

For the original untransposed ATLAS generators, these certificates check TB
and DA with T = A + B and D = T + TB, retaining all 1792 columns. Seven
adjacent 64-row certificates cover the interval; `BlockAssembly` supplies
the already checked block on rows 1536 through 1599. Every block connects
its literal masks to the published row lists.

These exports discharge the fourth-quarter premises of the full-list and
matrix consumers in `InitialProducts` and `InitialProducts.Consumer`.
See `source/README.md` and `../source/README.md` for the ATLAS attribution,
source expression, and checking conventions.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter3

theorem tb_checked :
    Wide.checkRows 1792 ((tRows.drop 1344).take 448)
      RightCertificate.wideSecond ((tbRows.drop 1344).take 448) = true :=
  tb_quarter3_of_blocks Block21.tb_checked Block22.tb_checked Block23.tb_checked
    Block25.tb_checked Block26.tb_checked Block27.tb_checked

theorem da_checked :
    Wide.checkRows 1792 ((dRows.drop 1344).take 448)
      RightCertificate.wideFirst ((daRows.drop 1344).take 448) = true :=
  da_quarter3_of_blocks Block21.da_checked Block22.da_checked Block23.da_checked
    Block25.da_checked Block26.da_checked Block27.da_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts.Quarter3
