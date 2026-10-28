module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks14
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks15
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks16
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks17
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks18
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks19
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks20

/-!
# Final left products on rows 896–1343

The seven exact 64-row certificates cover the third quarter of both products.
Each block checks the original DA masks and staged XOR masks for E against
the unchanged expanded second generator and fixed output rows. List slicing
and append composition preserve the full 1792-column checker.

These exports discharge the third-quarter premises of
`LeftCertificate.dab_checked_of_quarters` and
`LeftCertificate.left_checked_of_quarters`.
See `source/README.md` and `../source/README.md` for the ATLAS provenance
and the left singular-expression factorization.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter02

private theorem checkRows_slice_add (a w c : List Nat) (i k l : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) w ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 ((a.drop (i + k)).take l) w
      ((c.drop (i + k)).take l) = true) :
    Wide.checkRows 1792 ((a.drop i).take (k + l)) w
      ((c.drop i).take (k + l)) = true := by
  rw [List.take_add, List.take_add]
  apply Wide.checkRows_append
  · exact h₁
  · simpa only [List.drop_drop] using h₂

/-- The exact third-quarter check, with no numerical or matrix premises. -/
theorem dab_checked :
    Wide.checkRows 1792 ((daRows.drop 896).take 448) RightCertificate.wideSecond
      ((dabRows.drop 896).take 448) = true := by
  apply checkRows_slice_add daRows RightCertificate.wideSecond dabRows
    896 64 384 Block14.dab_checked
  apply checkRows_slice_add daRows RightCertificate.wideSecond dabRows
    960 64 320 Block15.dab_checked
  apply checkRows_slice_add daRows RightCertificate.wideSecond dabRows
    1024 64 256 Block16.dab_checked
  apply checkRows_slice_add daRows RightCertificate.wideSecond dabRows
    1088 64 192 Block17.dab_checked
  apply checkRows_slice_add daRows RightCertificate.wideSecond dabRows
    1152 64 128 Block18.dab_checked
  apply checkRows_slice_add daRows RightCertificate.wideSecond dabRows
    1216 64 64 Block19.dab_checked
  exact Block20.dab_checked

/-- The exact third-quarter check, with no numerical or matrix premises. -/
theorem left_checked :
    Wide.checkRows 1792 ((eRows.drop 896).take 448) RightCertificate.wideSecond
      ((leftRows.toList.drop 896).take 448) = true := by
  apply checkRows_slice_add eRows RightCertificate.wideSecond leftRows.toList
    896 64 384 Block14.left_checked
  apply checkRows_slice_add eRows RightCertificate.wideSecond leftRows.toList
    960 64 320 Block15.left_checked
  apply checkRows_slice_add eRows RightCertificate.wideSecond leftRows.toList
    1024 64 256 Block16.left_checked
  apply checkRows_slice_add eRows RightCertificate.wideSecond leftRows.toList
    1088 64 192 Block17.left_checked
  apply checkRows_slice_add eRows RightCertificate.wideSecond leftRows.toList
    1152 64 128 Block18.left_checked
  apply checkRows_slice_add eRows RightCertificate.wideSecond leftRows.toList
    1216 64 64 Block19.left_checked
  exact Block20.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter02
