module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Specialized
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Trees

/-!
# Applying the specialized sums to the literal product checker

The tree equalities identify the exact published expanded tables. Each row
uses a separately checked integer sum and 1792-column parity certificate.
The concrete consumers are the two product checks in each Checks module.
See source/README.md for the source expression and ATLAS conventions.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

theorem aFn_sound (a : Nat) : aFn a = Wide.sumRow a RightCertificate.wideFirst := by
  rw [aFn_eq, rowRec_eq, row_sound _ _ aValid, aFlatten]

theorem bFn_sound (a : Nat) : bFn a = Wide.sumRow a RightCertificate.wideSecond := by
  rw [bFn_eq, rowRec_eq, row_sound _ _ bValid, bFlatten]

theorem product_cons_a (a c s : Nat) (as cs : List Nat)
    (hs : aFn a = s) (hp : parityRec1792 s c = true)
    (ht : Wide.checkRows 1792 as RightCertificate.wideFirst cs = true) :
    Wide.checkRows 1792 (a :: as) RightCertificate.wideFirst (c :: cs) = true :=
  RightCertificate.product_cons a c s as _ cs
    (by simpa only [aFn_sound] using hs)
    (by simpa only [parityRec1792_eq, parity1792_eq] using hp) ht

theorem product_cons_b (a c s : Nat) (as cs : List Nat)
    (hs : bFn a = s) (hp : parityRec1792 s c = true)
    (ht : Wide.checkRows 1792 as RightCertificate.wideSecond cs = true) :
    Wide.checkRows 1792 (a :: as) RightCertificate.wideSecond (c :: cs) = true :=
  RightCertificate.product_cons a c s as _ cs
    (by simpa only [bFn_sound] using hs)
    (by simpa only [parityRec1792_eq, parity1792_eq] using hp) ht

/-- Concatenate adjacent bounded row certificates without evaluating the data. -/
theorem product_range (a w c : List Nat) (i k n : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) w ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 ((a.drop (i+k)).take n) w
      ((c.drop (i+k)).take n) = true) :
    Wide.checkRows 1792 ((a.drop i).take (k+n)) w
      ((c.drop i).take (k+n)) = true := by
  have h := Wide.checkRows_append 1792 ((a.drop i).take k)
    (((a.drop i).drop k).take n) w ((c.drop i).take k)
    (((c.drop i).drop k).take n) h₁
    (by simpa only [List.drop_drop, Nat.add_comm] using h₂)
  simpa only [← List.take_add] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts

