module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Rows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideFirst
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.Arithmetic

/-!
# Bounded assembly for the HA row certificate

Single-row sum and parity certificates imply the exact sequential checker.
Adjacent checked intervals combine by the checker's append theorem. The
concrete row lengths follow from the existing XOR construction of H.
These helpers are consumed by the HA blocks and their complete assembly.
See `source/README.md` for the original ATLAS convention and reproduction.
-/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.HaBlocks

private theorem take_drop_one (l : List Nat) (i : Nat) (hi : i < l.length) :
    (l.drop i).take 1 = [l[i]!] := by
  simp only [List.drop_eq_getElem_cons hi, List.take]
  rw [getElem!_pos l i hi]

theorem row_checked (a w c : List Nat) (i s : Nat)
    (ha : i < a.length) (hc : i < c.length)
    (hs : Wide.sumRow a[i]! w = s)
    (hp : Wide.checkParity 1792 s c[i]! = true) :
    Wide.checkRows 1792 ((a.drop i).take 1) w ((c.drop i).take 1) = true := by
  rw [take_drop_one a i ha, take_drop_one c i hc]
  exact product_cons _ _ s [] w [] hs hp rfl

theorem append_ranges (a w c : List Nat) (i k l : Nat)
    (h₁ : Wide.checkRows 1792 ((a.drop i).take k) w ((c.drop i).take k) = true)
    (h₂ : Wide.checkRows 1792 ((a.drop (i+k)).take l) w
      ((c.drop (i+k)).take l) = true) :
    Wide.checkRows 1792 ((a.drop i).take (k+l)) w ((c.drop i).take (k+l)) = true := by
  rw [List.take_add, List.take_add]
  exact Wide.checkRows_append 1792 _ _ _ _ _ h₁
    (by simpa only [List.drop_drop, Nat.add_comm] using h₂)

theorem h_length : hRows.length = 1792 := by
  have hAL : Data1792.firstRows.toList.length = 1792 := by decide +kernel
  have hBL : Data1792.secondRows.toList.length = 1792 := by decide +kernel
  have hBAL : baRows.length = 1792 := by decide +kernel
  have hUBL : ubRows.length = 1792 := by decide +kernel
  simp only [hRows, ibtRows, ibRows, tRows, List.length_zipWith, diagRows,
    List.length_ofFn, hAL, hBL, hBAL, hUBL, Nat.min_self]

theorem ha_length : haRows.length = 1792 := by decide +kernel

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate.HaBlocks
