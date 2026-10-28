module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks23
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Quarter00
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Quarter01
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Quarter02
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Quarter03

/-!
# Assembly of the final two left products

Four disjoint 448-row certificates cover every row and all 1792 columns.
Their inputs are the exact fixed lists used by `LeftExpression.Conditional`.
For the original ATLAS generators, these certify DAB = (DA)B and L = EB,
where E is the published packed XOR of D and DAB and L uses the fixed output
array. The unconditional checks require no expansion or earlier-product premise.
See `FinalProducts/source/README.md` for provenance and measured checks.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate

set_option maxRecDepth 8192 in
theorem dab_checked_of_quarters
    (h0 : Wide.checkRows 1792 ((daRows.drop 0).take 448)
      RightCertificate.wideSecond ((dabRows.drop 0).take 448) = true)
    (h1 : Wide.checkRows 1792 ((daRows.drop 448).take 448)
      RightCertificate.wideSecond ((dabRows.drop 448).take 448) = true)
    (h2 : Wide.checkRows 1792 ((daRows.drop 896).take 448)
      RightCertificate.wideSecond ((dabRows.drop 896).take 448) = true)
    (h3 : Wide.checkRows 1792 ((daRows.drop 1344).take 448)
      RightCertificate.wideSecond ((dabRows.drop 1344).take 448) = true)
    : Wide.checkRows 1792 daRows RightCertificate.wideSecond dabRows = true := by
  change Wide.checkRows 1792 (daRows.drop 0) RightCertificate.wideSecond (dabRows.drop 0) = true
  apply RightCertificate.product_step daRows RightCertificate.wideSecond dabRows 0 448 h0
  apply RightCertificate.product_step daRows RightCertificate.wideSecond dabRows 448 448 h1
  apply RightCertificate.product_step daRows RightCertificate.wideSecond dabRows 896 448 h2
  apply RightCertificate.product_step daRows RightCertificate.wideSecond dabRows 1344 448 h3
  decide +kernel

set_option maxRecDepth 8192 in
theorem left_checked_of_quarters
    (h0 : Wide.checkRows 1792 ((eRows.drop 0).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 0).take 448) = true)
    (h1 : Wide.checkRows 1792 ((eRows.drop 448).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 448).take 448) = true)
    (h2 : Wide.checkRows 1792 ((eRows.drop 896).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 896).take 448) = true)
    (h3 : Wide.checkRows 1792 ((eRows.drop 1344).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 1344).take 448) = true)
    : Wide.checkRows 1792 eRows RightCertificate.wideSecond leftRows.toList = true := by
  change Wide.checkRows 1792 (eRows.drop 0) RightCertificate.wideSecond (leftRows.toList.drop 0) = true
  apply RightCertificate.product_step eRows RightCertificate.wideSecond leftRows.toList 0 448 h0
  apply RightCertificate.product_step eRows RightCertificate.wideSecond leftRows.toList 448 448 h1
  apply RightCertificate.product_step eRows RightCertificate.wideSecond leftRows.toList 896 448 h2
  apply RightCertificate.product_step eRows RightCertificate.wideSecond leftRows.toList 1344 448 h3
  decide +kernel

/-- All rows and columns of the final intermediate product DAB = (DA)B. -/
theorem dab_checked :
    Wide.checkRows 1792 daRows RightCertificate.wideSecond dabRows = true :=
  dab_checked_of_quarters FinalProducts.Quarter00.dab_checked
    FinalProducts.Quarter01.dab_checked FinalProducts.Quarter02.dab_checked
    FinalProducts.Quarter03.dab_checked

/-- All rows and columns of EB against the unchanged final left-row array. -/
theorem left_checked :
    Wide.checkRows 1792 eRows RightCertificate.wideSecond leftRows.toList = true :=
  left_checked_of_quarters FinalProducts.Quarter00.left_checked
    FinalProducts.Quarter01.left_checked FinalProducts.Quarter02.left_checked
    FinalProducts.Quarter03.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate
