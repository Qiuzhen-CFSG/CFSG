module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.FinalProducts.TreeData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideSecond

/-! The complete balanced table is exactly the published `wideSecond`. -/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts

set_option maxRecDepth 8192 in
theorem secondTree_rows : secondTree.flatten = RightCertificate.wideSecond := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem secondTree_valid : secondTree.Valid := by
  apply SumTree.valid_of_check
  decide +kernel

theorem secondTree_sum (a : Nat) :
    secondTree.eval a = Wide.sumRow a RightCertificate.wideSecond := by
  rw [SumTree.eval_eq _ _ secondTree_valid, secondTree_rows]

theorem product_cons (a c s : Nat) (as cs : List Nat)
    (hs : secondTree.eval a = s) (hp : parityTree 8 7 s c = true)
    (ht : Wide.checkRows 1792 as RightCertificate.wideSecond cs = true) :
    Wide.checkRows 1792 (a :: as) RightCertificate.wideSecond (c :: cs) = true := by
  apply RightCertificate.product_cons a c s as RightCertificate.wideSecond cs
  · simpa only [secondTree_sum] using hs
  · simpa only [parityTree_eq, show 7 * 2^8 = 1792 by decide] using hp
  · exact ht

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.FinalProducts
