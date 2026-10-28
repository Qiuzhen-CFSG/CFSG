module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.Conditional

/-!
Apply the literal left-expression consumer with the full TB and DA checks
discharged. The two independent expansion checks and the final two products
remain explicit. The earlier conditional quarter interface is preserved.
See source/README.md for the source expression and remaining assembly owners.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open LeftCertificate

theorem packedLeft_eq_leftExpression_of_initial_quarters
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList RightCertificate.wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList RightCertificate.wideSecond = true)
    (hdab : Wide.checkRows 1792 daRows RightCertificate.wideSecond dabRows = true)
    (hl : Wide.checkRows 1792 eRows RightCertificate.wideSecond leftRows.toList = true)
    (tb0 : Wide.checkRows 1792 ((tRows.drop 0).take 448)
      RightCertificate.wideSecond ((tbRows.drop 0).take 448) = true)
    (tb1 : Wide.checkRows 1792 ((tRows.drop 448).take 448)
      RightCertificate.wideSecond ((tbRows.drop 448).take 448) = true)
    (tb2 : Wide.checkRows 1792 ((tRows.drop 896).take 448)
      RightCertificate.wideSecond ((tbRows.drop 896).take 448) = true)
    (tb3 : Wide.checkRows 1792 ((tRows.drop 1344).take 448)
      RightCertificate.wideSecond ((tbRows.drop 1344).take 448) = true)
    (da0 : Wide.checkRows 1792 ((dRows.drop 0).take 448)
      RightCertificate.wideFirst ((daRows.drop 0).take 448) = true)
    (da1 : Wide.checkRows 1792 ((dRows.drop 448).take 448)
      RightCertificate.wideFirst ((daRows.drop 448).take 448) = true)
    (da2 : Wide.checkRows 1792 ((dRows.drop 896).take 448)
      RightCertificate.wideFirst ((daRows.drop 896).take 448) = true)
    (da3 : Wide.checkRows 1792 ((dRows.drop 1344).take 448)
      RightCertificate.wideFirst ((daRows.drop 1344).take 448) = true)
    : packedLeft = leftExpression :=
  packedLeft_eq_leftExpression_of_checks hfirst hsecond
    (tb_checked_of_quarters tb0 tb1 tb2 tb3)
    (da_checked_of_quarters da0 da1 da2 da3) hdab hl

/-- Apply the two unconditional initial-product certificates to the exact
left-expression consumer, retaining only the independent remaining checks. -/
theorem packedLeft_eq_leftExpression_of_final_checks
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList RightCertificate.wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList RightCertificate.wideSecond = true)
    (hdab : Wide.checkRows 1792 daRows RightCertificate.wideSecond dabRows = true)
    (hl : Wide.checkRows 1792 eRows RightCertificate.wideSecond leftRows.toList = true) :
    packedLeft = leftExpression :=
  packedLeft_eq_leftExpression_of_checks hfirst hsecond tb_checked da_checked hdab hl

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix

