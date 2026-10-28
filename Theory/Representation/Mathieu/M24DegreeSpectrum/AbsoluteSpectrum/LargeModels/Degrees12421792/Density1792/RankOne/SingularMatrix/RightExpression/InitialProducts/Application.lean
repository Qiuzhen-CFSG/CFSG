module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.InitialProducts.BA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.InitialProducts.TB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.InitialProducts.UB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Conditional

/-!
# Application of the three initial product certificates

The exact right-expression consumer now needs only the two expansion checks
and the two final products. This theorem does not assert that those remaining
premises have been discharged. See `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open RightCertificate

/-- Discharge exactly the BA, TB and UB premises of the literal right-expression
assembly, retaining its four independent remaining checks. -/
theorem packedRight_eq_rightExpression_of_initialProducts
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList wideSecond = true)
    (hha : Wide.checkRows 1792 hRows wideFirst haRows = true)
    (hr : Wide.checkRows 1792 haRows wideSecond rightRows.toList = true) :
    packedRight = rightExpression :=
  packedRight_eq_rightExpression_of_checks hfirst hsecond ba_checked tb_checked ub_checked hha hr

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
