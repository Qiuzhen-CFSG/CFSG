module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks07
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks08
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks09
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks10
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks11
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks12
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.Checks13

/-!
# Final left-product checks on rows 448–895

The seven complete 64-row checks are joined by list append, preserving the
literal input and output slices and the fixed expanded second generator.
Every block checks all 1792 columns. These two unconditional certificates
discharge the second-quarter premises of `LeftCertificate.dab_checked_of_quarters`
and `LeftCertificate.left_checked_of_quarters`.
See `source/README.md` and `../source/README.md` for the factorization,
ATLAS provenance, and kernel-checked scalar evaluation.
-/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter01

private theorem take_step (a c : List Nat) (i k l : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) RightCertificate.wideSecond
      ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 ((a.drop (i+k)).take l) RightCertificate.wideSecond
      ((c.drop (i+k)).take l) = true) :
    Wide.checkRows 1792 ((a.drop i).take (k+l)) RightCertificate.wideSecond
      ((c.drop i).take (k+l)) = true := by
  rw [List.take_add, List.take_add]
  apply Wide.checkRows_append
  · exact h₁
  · simpa only [List.drop_drop, Nat.add_comm] using h₂

theorem dab_checked :
    Wide.checkRows 1792 ((daRows.drop 448).take 448) RightCertificate.wideSecond
      ((dabRows.drop 448).take 448) = true := by
  apply take_step daRows dabRows 448 64 384 Block07.dab_checked
  apply take_step daRows dabRows 512 64 320 Block08.dab_checked
  apply take_step daRows dabRows 576 64 256 Block09.dab_checked
  apply take_step daRows dabRows 640 64 192 Block10.dab_checked
  apply take_step daRows dabRows 704 64 128 Block11.dab_checked
  apply take_step daRows dabRows 768 64 64 Block12.dab_checked
  exact Block13.dab_checked

theorem left_checked :
    Wide.checkRows 1792 ((eRows.drop 448).take 448) RightCertificate.wideSecond
      ((leftRows.toList.drop 448).take 448) = true := by
  apply take_step eRows leftRows.toList 448 64 384 Block07.left_checked
  apply take_step eRows leftRows.toList 512 64 320 Block08.left_checked
  apply take_step eRows leftRows.toList 576 64 256 Block09.left_checked
  apply take_step eRows leftRows.toList 640 64 192 Block10.left_checked
  apply take_step eRows leftRows.toList 704 64 128 Block11.left_checked
  apply take_step eRows leftRows.toList 768 64 64 Block12.left_checked
  exact Block13.left_checked

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts.Quarter01
