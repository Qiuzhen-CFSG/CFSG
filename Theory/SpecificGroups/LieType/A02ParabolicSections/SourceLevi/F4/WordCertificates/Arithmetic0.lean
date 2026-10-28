module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.WordCertificates.Rows

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

private theorem product0_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 0)[i.val]! (generatorRows 0) 52 = 2 ^ i.val := by
  decide +kernel

theorem product0 : Thompson.BinaryMatrix.decode 52 (generatorRows 0) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 0) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 0) (generatorRows 0) product0_check

private theorem product1_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 1)[i.val]! (generatorRows 1) 52 = 2 ^ i.val := by
  decide +kernel

theorem product1 : Thompson.BinaryMatrix.decode 52 (generatorRows 1) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 1) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 1) (generatorRows 1) product1_check

private theorem product2_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! (generatorRows 2) 52 = 2 ^ i.val := by
  decide +kernel

theorem product2 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 2) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 2) (generatorRows 2) product2_check

private theorem product3_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! (generatorRows 3) 52 = 2 ^ i.val := by
  decide +kernel

theorem product3 : Thompson.BinaryMatrix.decode 52 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 3) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 3) (generatorRows 3) product3_check

private theorem product4_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! (generatorRows 4) 52 = 2 ^ i.val := by
  decide +kernel

theorem product4 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 4) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 4) (generatorRows 4) product4_check

private theorem product5_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 5)[i.val]! (generatorRows 5) 52 = 2 ^ i.val := by
  decide +kernel

theorem product5 : Thompson.BinaryMatrix.decode 52 (generatorRows 5) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 5) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 5) (generatorRows 5) product5_check

private theorem product6_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 6)[i.val]! (generatorRows 6) 52 = 2 ^ i.val := by
  decide +kernel

theorem product6 : Thompson.BinaryMatrix.decode 52 (generatorRows 6) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 6) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 6) (generatorRows 6) product6_check

private theorem product7_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 7)[i.val]! (generatorRows 7) 52 = 2 ^ i.val := by
  decide +kernel

theorem product7 : Thompson.BinaryMatrix.decode 52 (generatorRows 7) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 7) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 (generatorRows 7) (generatorRows 7) product7_check

private theorem product8_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! (generatorRows 3) 52 = rows0[i.val]! := by
  decide +kernel

theorem product8 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 (generatorRows 3) = Thompson.BinaryMatrix.decode 52 rows0 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) (generatorRows 3) rows0 product8_check

private theorem product9_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! rows0 52 = rows1[i.val]! := by
  decide +kernel

theorem product9 : Thompson.BinaryMatrix.decode 52 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 52 rows0 = Thompson.BinaryMatrix.decode 52 rows1 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 3) rows0 rows1 product9_check

private theorem product10_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows1 52 = rows2[i.val]! := by
  decide +kernel

theorem product10 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 rows1 = Thompson.BinaryMatrix.decode 52 rows2 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 4) rows1 rows2 product10_check

private theorem product11_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 5)[i.val]! rows2 52 = rows3[i.val]! := by
  decide +kernel

theorem product11 : Thompson.BinaryMatrix.decode 52 (generatorRows 5) *
    Thompson.BinaryMatrix.decode 52 rows2 = Thompson.BinaryMatrix.decode 52 rows3 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 5) rows2 rows3 product11_check

private theorem product12_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! rows3 52 = rows4[i.val]! := by
  decide +kernel

theorem product12 : Thompson.BinaryMatrix.decode 52 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 52 rows3 = Thompson.BinaryMatrix.decode 52 rows4 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 3) rows3 rows4 product12_check

private theorem product13_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows4 52 = rows5[i.val]! := by
  decide +kernel

theorem product13 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows4 = Thompson.BinaryMatrix.decode 52 rows5 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows4 rows5 product13_check

private theorem product14_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows5 52 = rows6[i.val]! := by
  decide +kernel

theorem product14 : Thompson.BinaryMatrix.decode 52 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 52 rows5 = Thompson.BinaryMatrix.decode 52 rows6 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 4) rows5 rows6 product14_check

private theorem product15_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! rows6 52 = rows7[i.val]! := by
  decide +kernel

theorem product15 : Thompson.BinaryMatrix.decode 52 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 52 rows6 = Thompson.BinaryMatrix.decode 52 rows7 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 3) rows6 rows7 product15_check

end Theory.SpecificGroups.LieType.SourceLevi.F4.WordCertificates.Checked
