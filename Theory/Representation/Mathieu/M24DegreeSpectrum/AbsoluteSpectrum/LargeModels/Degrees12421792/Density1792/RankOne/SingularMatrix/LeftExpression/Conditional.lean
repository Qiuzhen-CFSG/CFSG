module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.Rows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideFirst
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideSecond
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.ProductCriteria

/-!
# Four-product assembly of the left singular expression

For the literal ATLAS pair put T=A+B, D=T+TB, E=D+(DA)B. Distributivity
identifies EB with precisely the first and fourth summands of the singular
expression. Packed XOR supplies all additions structurally. The four products
and the two expanded-table checks remain explicit numerical obligations.
This is the left premise of `packedSingular_eq_singular_of_parts`, not an
unconditional certificate. See `source/README.md` for provenance and consumers.
-/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open Thompson.BinaryMatrix LeftCertificate

private theorem assemble (A B t tb d da dab e l : Matrix (Fin 1792) (Fin 1792) (ZMod 2))
    (ht : A + B = t) (htb : t * B = tb) (hd : t + tb = d)
    (hda : d * A = da) (hdab : da * B = dab) (he : d + dab = e) (hl : e * B = l) :
    l = (A + A*B + B + B*B) * (A*B*B) + (A + A*B + B + B*B) * B := by
  rw [← hl, ← he, ← hdab, ← hda, ← hd, ← htb, ← ht]
  simp only [add_mul, mul_assoc]
  abel

/-- Exact assembly from four matrix products; all rowwise additions are proved
structurally. The original untransposed generators and fixed output are used. -/
theorem packedLeft_eq_leftExpression_of_products
    (htb : decode 1792 tRows.toArray * Data1792.second = decode 1792 tbRows.toArray)
    (hda : decode 1792 dRows.toArray * Data1792.first = decode 1792 daRows.toArray)
    (hdab : decode 1792 daRows.toArray * Data1792.second = decode 1792 dabRows.toArray)
    (hl : decode 1792 eRows.toArray * Data1792.second = packedLeft) :
    packedLeft = leftExpression := by
  have hAL : Data1792.firstRows.toList.length = 1792 := by decide +kernel
  have hBL : Data1792.secondRows.toList.length = 1792 := by decide +kernel
  have hTBL : tbRows.length = 1792 := by decide +kernel
  have hDABL : dabRows.length = 1792 := by decide +kernel
  have hTL : tRows.length = 1792 := by
    simp only [tRows, List.length_zipWith, hAL, hBL, Nat.min_self]
  have hDL : dRows.length = 1792 := by
    simp only [dRows, List.length_zipWith, hTL, hTBL, Nat.min_self]
  have ht := (RightCertificate.decode_zipWith_xor 1792 _ _ hAL hBL).symm
  have hd := (RightCertificate.decode_zipWith_xor 1792 _ _ hTL hTBL).symm
  have he := (RightCertificate.decode_zipWith_xor 1792 _ _ hDL hDABL).symm
  change Data1792.first + Data1792.second = decode 1792 tRows.toArray at ht
  change decode 1792 tRows.toArray + decode 1792 tbRows.toArray = decode 1792 dRows.toArray at hd
  change decode 1792 dRows.toArray + decode 1792 dabRows.toArray = decode 1792 eRows.toArray at he
  exact assemble _ _ _ _ _ _ _ _ _ ht htb hd hda hdab he hl

/-- The carry-free checker applied to exactly the four products. The expansion
checks concern the shared tables already used by the independent right part. -/
theorem packedLeft_eq_leftExpression_of_checks
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList RightCertificate.wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList RightCertificate.wideSecond = true)
    (htb : Wide.checkRows 1792 tRows RightCertificate.wideSecond tbRows = true)
    (hda : Wide.checkRows 1792 dRows RightCertificate.wideFirst daRows = true)
    (hdab : Wide.checkRows 1792 daRows RightCertificate.wideSecond dabRows = true)
    (hl : Wide.checkRows 1792 eRows RightCertificate.wideSecond leftRows.toList = true) :
    packedLeft = leftExpression := by
  have hAL : Data1792.firstRows.toList.length = 1792 := by decide +kernel
  have hBL : Data1792.secondRows.toList.length = 1792 := by decide +kernel
  have hTBL : tbRows.length = 1792 := by decide +kernel
  have hDABL : dabRows.length = 1792 := by decide +kernel
  have hTL : tRows.length = 1792 := by
    simp only [tRows, List.length_zipWith, hAL, hBL, Nat.min_self]
  have hDL : dRows.length = 1792 := by
    simp only [dRows, List.length_zipWith, hTL, hTBL, Nat.min_self]
  have hEL : eRows.length = 1792 := by
    simp only [eRows, List.length_zipWith, hDL, hDABL, Nat.min_self]
  exact packedLeft_eq_leftExpression_of_products
    (mul_second_of_checks _ _ _ hTL hsecond htb)
    (mul_first_of_checks _ _ _ hDL hfirst hda)
    (mul_second_of_checks _ _ _ (by decide +kernel) hsecond hdab)
    (mul_second_of_checks _ _ _ hEL hsecond hl)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
