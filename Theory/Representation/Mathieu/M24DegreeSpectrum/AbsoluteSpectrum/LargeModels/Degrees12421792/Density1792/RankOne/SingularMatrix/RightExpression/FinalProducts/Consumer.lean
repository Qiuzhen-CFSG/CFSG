module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.FinalProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Conditional

/-!
# Applying the final products to the exact right expression

The full HA and HA*B certificates discharge the last two premises of
`packedRight_eq_rightExpression_of_checks` for the unchanged ATLAS generators.
The expansion checks and BA, TB, UB products remain explicit here. Their producers
are `qt-k04-m24-1792-right-wide-expansions` and
`qt-k04-m24-1792-right-initial-products`; unconditional assembly remains with
`qt-k04-m24-1792-singular-right-part`.

See `../source/README.md` for the five-product factorization and source attribution.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open RightCertificate

/-- The exact right expression after discharging both final product checks.
Only the two table expansions and the first three products remain as premises. -/
theorem packedRight_eq_rightExpression_of_initial_checks
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList wideSecond = true)
    (hba : Wide.checkRows 1792 Data1792.secondRows.toList wideFirst baRows = true)
    (htb : Wide.checkRows 1792 tRows wideSecond tbRows = true)
    (hub : Wide.checkRows 1792 uRows wideSecond ubRows = true) :
    packedRight = rightExpression :=
  packedRight_eq_rightExpression_of_checks hfirst hsecond hba htb hub
    ha_checked right_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
