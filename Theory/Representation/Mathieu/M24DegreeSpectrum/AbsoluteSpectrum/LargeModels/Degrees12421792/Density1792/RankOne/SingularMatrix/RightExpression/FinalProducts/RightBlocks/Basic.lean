module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Rows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideSecond
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic
/-!
# Assembly of the final right-product row certificates

The single-row bridge explicitly identifies the list indexing of the fixed
array with its array indexing. Bounded intervals then compose by the existing
carry-free product checker. The concrete consumer is `RightCertificate.right_checked`,
which discharges the final product premise of `RightExpression.Conditional`.
See `../../source/README.md` for the exact ATLAS product and its provenance.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.RightBlocks
private theorem take_drop_one (l : List Nat) (i : Nat) (hi : i < l.length) :
    (l.drop i).take 1 = [l[i]!] := by
  simp only [List.drop_eq_getElem_cons hi, List.take]
  rw [getElem!_pos l i hi]

set_option maxRecDepth 8192 in
theorem ha_length : haRows.length = 1792 := by decide +kernel
set_option maxRecDepth 8192 in
theorem right_size : rightRows.size = 1792 := by decide +kernel

theorem single_checked (i s : Nat) (hi : i < 1792)
    (hs : Wide.sumRow haRows[i]! wideSecond = s)
    (hp : Wide.checkParity 1792 s rightRows[i]! = true) :
    Wide.checkRows 1792 ((haRows.drop i).take 1) wideSecond
      ((rightRows.toList.drop i).take 1) = true := by
  have ha : i < haRows.length := by simpa only [ha_length] using hi
  have hr : i < rightRows.size := by simpa only [right_size] using hi
  have hrl : i < rightRows.toList.length := by simpa only [Array.length_toList] using hr
  have hri : rightRows.toList[i]! = rightRows[i]! := by
    rw [getElem!_pos rightRows.toList i hrl, Array.getElem_toList,
      getElem!_pos rightRows i hr]
  rw [take_drop_one haRows i ha, take_drop_one rightRows.toList i hrl]
  exact product_cons _ _ s [] wideSecond [] hs (by rw [hri]; exact hp) rfl

theorem append_checked (i m n : Nat)
    (hm : Wide.checkRows 1792 ((haRows.drop i).take m) wideSecond
      ((rightRows.toList.drop i).take m) = true)
    (hn : Wide.checkRows 1792 ((haRows.drop (i+m)).take n) wideSecond
      ((rightRows.toList.drop (i+m)).take n) = true) :
    Wide.checkRows 1792 ((haRows.drop i).take (m+n)) wideSecond
      ((rightRows.toList.drop i).take (m+n)) = true := by
  simpa only [List.take_add, List.drop_drop, Nat.add_comm] using
    Wide.checkRows_append 1792 ((haRows.drop i).take m) ((haRows.drop (i+m)).take n)
      wideSecond ((rightRows.toList.drop i).take m)
      ((rightRows.toList.drop (i+m)).take n) hm hn
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.RightBlocks
