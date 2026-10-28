module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.Conditional

/-!
# Application of the complete final-product checks

The checked DAB and EB products discharge the final two premises of the exact
left-expression consumer. Only the two expanded-table checks and the earlier
TB and DA products remain explicit in `packedLeft_eq_leftExpression_of_initial_checks`.
The original quarter-conditional interface is preserved. See `source/README.md`
for the factorization, provenance and remaining assembly ownership.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open LeftCertificate

theorem packedLeft_eq_leftExpression_of_final_quarters
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList RightCertificate.wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList RightCertificate.wideSecond = true)
    (htb : Wide.checkRows 1792 tRows RightCertificate.wideSecond tbRows = true)
    (hda : Wide.checkRows 1792 dRows RightCertificate.wideFirst daRows = true)
    (dab0 : Wide.checkRows 1792 ((daRows.drop 0).take 448)
      RightCertificate.wideSecond ((dabRows.drop 0).take 448) = true)
    (dab1 : Wide.checkRows 1792 ((daRows.drop 448).take 448)
      RightCertificate.wideSecond ((dabRows.drop 448).take 448) = true)
    (dab2 : Wide.checkRows 1792 ((daRows.drop 896).take 448)
      RightCertificate.wideSecond ((dabRows.drop 896).take 448) = true)
    (dab3 : Wide.checkRows 1792 ((daRows.drop 1344).take 448)
      RightCertificate.wideSecond ((dabRows.drop 1344).take 448) = true)
    (left0 : Wide.checkRows 1792 ((eRows.drop 0).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 0).take 448) = true)
    (left1 : Wide.checkRows 1792 ((eRows.drop 448).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 448).take 448) = true)
    (left2 : Wide.checkRows 1792 ((eRows.drop 896).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 896).take 448) = true)
    (left3 : Wide.checkRows 1792 ((eRows.drop 1344).take 448)
      RightCertificate.wideSecond ((leftRows.toList.drop 1344).take 448) = true)
    : packedLeft = leftExpression :=
  packedLeft_eq_leftExpression_of_checks hfirst hsecond htb hda
    (dab_checked_of_quarters dab0 dab1 dab2 dab3)
    (left_checked_of_quarters left0 left1 left2 left3)

/-- The final-product certificates discharge exactly the DAB and EB checks.
The left-expression assembly owner retains the expansion and initial products. -/
theorem packedLeft_eq_leftExpression_of_initial_checks
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList RightCertificate.wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList RightCertificate.wideSecond = true)
    (htb : Wide.checkRows 1792 tRows RightCertificate.wideSecond tbRows = true)
    (hda : Wide.checkRows 1792 dRows RightCertificate.wideFirst daRows = true) :
    packedLeft = leftExpression :=
  packedLeft_eq_leftExpression_of_checks hfirst hsecond htb hda
    LeftCertificate.dab_checked LeftCertificate.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
