module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.WordCertificates.Arithmetic1

/-!
# Checked binary E₆ root words

The matrices use six Cartan coordinates followed by the 72 roots in the
source coordinate order. The eight generators are folded signed roots
at nodes 3, 2, {1,4}, {0,5}, in this order. Packed row products are verified
by Lean's kernel using `Thompson.BinaryMatrix.decode_mul`.

The source Levi producer compares these tables with the literal integral
Chevalley root operators. The seven words are the full ATLAS S62G1-P1.M
presentation; the source application is Aschbacher–Smith A.2.18, p.40.
-/

public section
namespace Theory.SpecificGroups.LieType.SourceLevi.E6.WordCertificates.Checked

private theorem product32_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! rows20 78 = rows21[i.val]! := by
  decide +kernel

theorem product32 : Thompson.BinaryMatrix.decode 78 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 78 rows20 = Thompson.BinaryMatrix.decode 78 rows21 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 3) rows20 rows21 product32_check

private theorem product33_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows21 78 = rows22[i.val]! := by
  decide +kernel

theorem product33 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows21 = Thompson.BinaryMatrix.decode 78 rows22 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows21 rows22 product33_check

private theorem product34_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 6)[i.val]! rows22 78 = rows23[i.val]! := by
  decide +kernel

theorem product34 : Thompson.BinaryMatrix.decode 78 (generatorRows 6) *
    Thompson.BinaryMatrix.decode 78 rows22 = Thompson.BinaryMatrix.decode 78 rows23 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 6) rows22 rows23 product34_check

private theorem product35_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 7)[i.val]! rows23 78 = rows24[i.val]! := by
  decide +kernel

theorem product35 : Thompson.BinaryMatrix.decode 78 (generatorRows 7) *
    Thompson.BinaryMatrix.decode 78 rows23 = Thompson.BinaryMatrix.decode 78 rows24 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 7) rows23 rows24 product35_check

private theorem product36_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 6)[i.val]! rows24 78 = rows25[i.val]! := by
  decide +kernel

theorem product36 : Thompson.BinaryMatrix.decode 78 (generatorRows 6) *
    Thompson.BinaryMatrix.decode 78 rows24 = Thompson.BinaryMatrix.decode 78 rows25 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 6) rows24 rows25 product36_check

private theorem product37_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows25 78 = rows26[i.val]! := by
  decide +kernel

theorem product37 : Thompson.BinaryMatrix.decode 78 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 78 rows25 = Thompson.BinaryMatrix.decode 78 rows26 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 4) rows25 rows26 product37_check

private theorem product38_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 5)[i.val]! rows26 78 = rows27[i.val]! := by
  decide +kernel

theorem product38 : Thompson.BinaryMatrix.decode 78 (generatorRows 5) *
    Thompson.BinaryMatrix.decode 78 rows26 = Thompson.BinaryMatrix.decode 78 rows27 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 5) rows26 rows27 product38_check

private theorem product39_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 4)[i.val]! rows27 78 = rows28[i.val]! := by
  decide +kernel

theorem product39 : Thompson.BinaryMatrix.decode 78 (generatorRows 4) *
    Thompson.BinaryMatrix.decode 78 rows27 = Thompson.BinaryMatrix.decode 78 rows28 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 4) rows27 rows28 product39_check

private theorem product40_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows28 78 = rows29[i.val]! := by
  decide +kernel

theorem product40 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows28 = Thompson.BinaryMatrix.decode 78 rows29 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows28 rows29 product40_check

private theorem product41_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 3)[i.val]! rows29 78 = rows30[i.val]! := by
  decide +kernel

theorem product41 : Thompson.BinaryMatrix.decode 78 (generatorRows 3) *
    Thompson.BinaryMatrix.decode 78 rows29 = Thompson.BinaryMatrix.decode 78 rows30 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 3) rows29 rows30 product41_check

private theorem product42_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows30 78 = rows31[i.val]! := by
  decide +kernel

theorem product42 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows30 = Thompson.BinaryMatrix.decode 78 rows31 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows30 rows31 product42_check

private theorem product43_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 0)[i.val]! rows31 78 = rows32[i.val]! := by
  decide +kernel

theorem product43 : Thompson.BinaryMatrix.decode 78 (generatorRows 0) *
    Thompson.BinaryMatrix.decode 78 rows31 = Thompson.BinaryMatrix.decode 78 rows32 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 0) rows31 rows32 product43_check

private theorem product44_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 1)[i.val]! rows32 78 = rows33[i.val]! := by
  decide +kernel

theorem product44 : Thompson.BinaryMatrix.decode 78 (generatorRows 1) *
    Thompson.BinaryMatrix.decode 78 rows32 = Thompson.BinaryMatrix.decode 78 rows33 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 1) rows32 rows33 product44_check

private theorem product45_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 0)[i.val]! rows33 78 = rows34[i.val]! := by
  decide +kernel

theorem product45 : Thompson.BinaryMatrix.decode 78 (generatorRows 0) *
    Thompson.BinaryMatrix.decode 78 rows33 = Thompson.BinaryMatrix.decode 78 rows34 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 0) rows33 rows34 product45_check

private theorem product46_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows17[i.val]! rows35 78 = 2 ^ i.val := by
  decide +kernel

theorem product46 : Thompson.BinaryMatrix.decode 78 rows17 *
    Thompson.BinaryMatrix.decode 78 rows35 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows17 rows35 product46_check

private theorem product47_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows34[i.val]! rows36 78 = 2 ^ i.val := by
  decide +kernel

theorem product47 : Thompson.BinaryMatrix.decode 78 rows34 *
    Thompson.BinaryMatrix.decode 78 rows36 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows34 rows36 product47_check

end Theory.SpecificGroups.LieType.SourceLevi.E6.WordCertificates.Checked
