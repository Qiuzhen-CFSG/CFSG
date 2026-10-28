module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.WordCertificates.Arithmetic0

/-!
# Checked binary F₄ root words

The matrices use four Cartan coordinates followed by the 48 roots in the
`ReeF4.CartanFieldAction.FieldSeparation.TraceValues.Coordinates` order.
Generator indices are the positive and negative parameter-one simple roots,
in the order 0+, 0−, 1+, 1−, 2+, 2−, 3+, 3−. Packed row products are verified
by Lean's kernel using `Thompson.BinaryMatrix.decode_mul`.

The source Levi producer compares these tables with the literal integral
Chevalley root operators. The seven words are the full ATLAS S62G1-P1.M
presentation; the source application is Aschbacher–Smith A.2.18, p.40.
-/

public section
namespace Theory.SpecificGroups.LieType.SourceLevi.F4.WordCertificates.Checked

private theorem product16_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 7)[i.val]! rows7 52 = rows8[i.val]! := by
  decide +kernel

theorem product16 : Thompson.BinaryMatrix.decode 52 (generatorRows 7) *
    Thompson.BinaryMatrix.decode 52 rows7 = Thompson.BinaryMatrix.decode 52 rows8 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 7) rows7 rows8 product16_check

private theorem product17_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 6)[i.val]! rows8 52 = rows9[i.val]! := by
  decide +kernel

theorem product17 : Thompson.BinaryMatrix.decode 52 (generatorRows 6) *
    Thompson.BinaryMatrix.decode 52 rows8 = Thompson.BinaryMatrix.decode 52 rows9 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 6) rows8 rows9 product17_check

private theorem product18_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 5)[i.val]! rows9 52 = rows10[i.val]! := by
  decide +kernel

theorem product18 : Thompson.BinaryMatrix.decode 52 (generatorRows 5) *
    Thompson.BinaryMatrix.decode 52 rows9 = Thompson.BinaryMatrix.decode 52 rows10 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 5) rows9 rows10 product18_check

private theorem product19_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows10 52 = rows11[i.val]! := by
  decide +kernel

theorem product19 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 rows10 = Thompson.BinaryMatrix.decode 52 rows11 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 4) rows10 rows11 product19_check

private theorem product20_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! rows11 52 = rows12[i.val]! := by
  decide +kernel

theorem product20 : Thompson.BinaryMatrix.decode 52 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 52 rows11 = Thompson.BinaryMatrix.decode 52 rows12 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 3) rows11 rows12 product20_check

private theorem product21_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 5)[i.val]! rows12 52 = rows13[i.val]! := by
  decide +kernel

theorem product21 : Thompson.BinaryMatrix.decode 52 (generatorRows 5) *
    Thompson.BinaryMatrix.decode 52 rows12 = Thompson.BinaryMatrix.decode 52 rows13 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 5) rows12 rows13 product21_check

private theorem product22_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 7)[i.val]! rows13 52 = rows14[i.val]! := by
  decide +kernel

theorem product22 : Thompson.BinaryMatrix.decode 52 (generatorRows 7) *
    Thompson.BinaryMatrix.decode 52 rows13 = Thompson.BinaryMatrix.decode 52 rows14 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 7) rows13 rows14 product22_check

private theorem product23_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows14 52 = rows15[i.val]! := by
  decide +kernel

theorem product23 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows14 = Thompson.BinaryMatrix.decode 52 rows15 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows14 rows15 product23_check

private theorem product24_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows15 52 = rows16[i.val]! := by
  decide +kernel

theorem product24 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 rows15 = Thompson.BinaryMatrix.decode 52 rows16 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 4) rows15 rows16 product24_check

private theorem product25_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 6)[i.val]! rows16 52 = rows17[i.val]! := by
  decide +kernel

theorem product25 : Thompson.BinaryMatrix.decode 52 (generatorRows 6) *
    Thompson.BinaryMatrix.decode 52 rows16 = Thompson.BinaryMatrix.decode 52 rows17 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 6) rows16 rows17 product25_check

private theorem product26_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! (generatorRows 2) 52 = rows18[i.val]! := by
  decide +kernel

theorem product26 : Thompson.BinaryMatrix.decode 52 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 2) = Thompson.BinaryMatrix.decode 52 rows18 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 3) (generatorRows 2) rows18 product26_check

private theorem product27_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows18 52 = rows1[i.val]! := by
  decide +kernel

theorem product27 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows18 = Thompson.BinaryMatrix.decode 52 rows1 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows18 rows1 product27_check

private theorem product28_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows1 52 = rows2[i.val]! := by
  decide +kernel

theorem product28 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 rows1 = Thompson.BinaryMatrix.decode 52 rows2 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 4) rows1 rows2 product28_check

private theorem product29_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 5)[i.val]! rows2 52 = rows3[i.val]! := by
  decide +kernel

theorem product29 : Thompson.BinaryMatrix.decode 52 (generatorRows 5) *
    Thompson.BinaryMatrix.decode 52 rows2 = Thompson.BinaryMatrix.decode 52 rows3 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 5) rows2 rows3 product29_check

private theorem product30_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows3 52 = rows19[i.val]! := by
  decide +kernel

theorem product30 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 rows3 = Thompson.BinaryMatrix.decode 52 rows19 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 4) rows3 rows19 product30_check

private theorem product31_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows19 52 = rows20[i.val]! := by
  decide +kernel

theorem product31 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows19 = Thompson.BinaryMatrix.decode 52 rows20 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows19 rows20 product31_check

end Theory.SpecificGroups.LieType.SourceLevi.F4.WordCertificates.Checked
