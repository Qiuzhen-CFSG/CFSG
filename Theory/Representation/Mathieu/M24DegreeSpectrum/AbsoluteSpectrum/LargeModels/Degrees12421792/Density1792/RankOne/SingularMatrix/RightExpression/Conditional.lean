module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Rows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideFirst
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideSecond
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.ProductCriteria

/-!
# Five-product assembly of the right singular expression

Put T = A + BA, U = TB + BA and H = 1 + B + T + UB. Then H(AB) is
exactly the second plus third summands of the published singular expression.
Packed XOR is interpreted structurally as matrix addition. The five products and two expanded-table
checks remain explicit, independent numerical obligations. This conditional
result supplies the exact right-part premise of `packedSingular_eq_singular_of_parts`.
It asserts no unconditional product identity. See `source/README.md`.
-/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
open Thompson.BinaryMatrix RightCertificate

private theorem assemble (A B ba t tb u ub h ha r : Matrix (Fin 1792) (Fin 1792) (ZMod 2))
    (hba : B * A = ba) (ht : A + ba = t) (htb : t * B = tb)
    (hu : tb + ba = u) (hub : u * B = ub) (hh : 1 + B + t + ub = h)
    (hha : h * A = ha) (hr : ha * B = r) :
    r = (1 + A + A*B*B + B) * (A*B) + (B*A + B*A*B + B*A*B*B) * (A*B) := by
  rw [← hr, ← hha, ← hh, ← hub, ← hu, ← htb, ← ht, ← hba]
  simp only [add_mul, one_mul, mul_assoc]
  abel

/-- Exact assembly from the two table checks and the five literal products.
No group-theoretic, density, rank, action or kernel assumption is used. -/
theorem packedRight_eq_rightExpression_of_checks
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList wideSecond = true)
    (hba : Wide.checkRows 1792 Data1792.secondRows.toList wideFirst baRows = true)
    (htb : Wide.checkRows 1792 tRows wideSecond tbRows = true)
    (hub : Wide.checkRows 1792 uRows wideSecond ubRows = true)
    (hha : Wide.checkRows 1792 hRows wideFirst haRows = true)
    (hr : Wide.checkRows 1792 haRows wideSecond rightRows.toList = true) :
    packedRight = rightExpression := by
  have hAL : Data1792.firstRows.toList.length = 1792 := by decide +kernel
  have hBL : Data1792.secondRows.toList.length = 1792 := by decide +kernel
  have hBAL : baRows.length = 1792 := by decide +kernel
  have hTBL : tbRows.length = 1792 := by decide +kernel
  have hUBL : ubRows.length = 1792 := by decide +kernel
  have hTL : tRows.length = 1792 := by simp only [tRows, List.length_zipWith, hAL, hBAL, Nat.min_self]
  have hDL : (diagRows 1792).length = 1792 := by simp only [diagRows, List.length_ofFn]
  have hIBL : ibRows.length = 1792 := by
    simp only [ibRows, List.length_zipWith, hDL, hBL, Nat.min_self]
  have hIBTL : ibtRows.length = 1792 := by simp only [ibtRows, List.length_zipWith, hIBL, hTL, Nat.min_self]
  have hUL : uRows.length = 1792 := by simp only [uRows, List.length_zipWith, hTBL, hBAL, Nat.min_self]
  have hHL : hRows.length = 1792 := by simp only [hRows, List.length_zipWith, hIBTL, hUBL, Nat.min_self]
  have hBA := mul_first_of_checks _ _ _ (by decide +kernel) hfirst hba
  have hTB := mul_second_of_checks _ _ _ hTL hsecond htb
  have hUB := mul_second_of_checks _ _ _ hUL hsecond hub
  have hHA := mul_first_of_checks _ _ _ hHL hfirst hha
  have hR := mul_second_of_checks _ _ _ (by decide +kernel) hsecond hr
  have hT := (decode_zipWith_xor 1792 _ _ hAL hBAL).symm
  have hU := (decode_zipWith_xor 1792 _ _ hTBL hBAL).symm
  have hIB := (decode_zipWith_xor 1792 (diagRows 1792) _ hDL hBL).symm
  rw [decode_diagRows] at hIB
  have hIBT := (decode_zipWith_xor 1792 _ _ hIBL hTL).symm
  have hH := (decode_zipWith_xor 1792 _ _ hIBTL hUBL).symm
  change decode 1792 tbRows.toArray + decode 1792 baRows.toArray = decode 1792 uRows.toArray at hU
  change decode 1792 ibRows.toArray + decode 1792 tRows.toArray = decode 1792 ibtRows.toArray at hIBT
  change decode 1792 ibtRows.toArray + decode 1792 ubRows.toArray = decode 1792 hRows.toArray at hH
  change Data1792.second * Data1792.first = decode 1792 baRows.toArray at hBA
  change Data1792.first + decode 1792 baRows.toArray = decode 1792 tRows.toArray at hT
  change 1 + Data1792.second = decode 1792 ibRows.toArray at hIB
  change decode 1792 haRows.toArray * Data1792.second = packedRight at hR
  have hh : 1 + Data1792.second + decode 1792 tRows.toArray + decode 1792 ubRows.toArray =
      decode 1792 hRows.toArray :=
    (congrArg (fun X => X + decode 1792 ubRows.toArray)
      ((congrArg (fun X => X + decode 1792 tRows.toArray) hIB).trans hIBT)).trans hH
  exact assemble _ _ _ _ _ _ _ _ _ _ hBA hT hTB hU hUB hh hHA hR

/-- The same literal matrix application when the five products are certified
with explicit, checked integer sums. Expansion checks are still required. -/
theorem packedRight_eq_rightExpression_of_witnessChecks
    (sBA sTB sUB sHA sR : List Nat)
    (hfirst : Wide.checkSpreadRows 1792 Data1792.firstRows.toList wideFirst = true)
    (hsecond : Wide.checkSpreadRows 1792 Data1792.secondRows.toList wideSecond = true)
    (hba : checkWitnessRows Data1792.secondRows.toList wideFirst baRows sBA = true)
    (htb : checkWitnessRows tRows wideSecond tbRows sTB = true)
    (hub : checkWitnessRows uRows wideSecond ubRows sUB = true)
    (hha : checkWitnessRows hRows wideFirst haRows sHA = true)
    (hr : checkWitnessRows haRows wideSecond rightRows.toList sR = true) :
    packedRight = rightExpression :=
  packedRight_eq_rightExpression_of_checks hfirst hsecond
    (checkWitnessRows_sound _ _ _ _ hba)
    (checkWitnessRows_sound _ _ _ _ htb)
    (checkWitnessRows_sound _ _ _ _ hub)
    (checkWitnessRows_sound _ _ _ _ hha)
    (checkWitnessRows_sound _ _ _ _ hr)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix
