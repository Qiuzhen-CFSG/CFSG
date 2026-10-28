module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.WordCertificates.Arithmetic2

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

private theorem product48_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows34[i.val]! (generatorRows 0) 78 = rows37[i.val]! := by
  decide +kernel

theorem product48 : Thompson.BinaryMatrix.decode 78 rows34 *
    Thompson.BinaryMatrix.decode 78 (generatorRows 0) = Thompson.BinaryMatrix.decode 78 rows37 :=
  Thompson.BinaryMatrix.decode_mul 78 rows34 (generatorRows 0) rows37 product48_check

private theorem product49_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows37[i.val]! rows36 78 = rows38[i.val]! := by
  decide +kernel

theorem product49 : Thompson.BinaryMatrix.decode 78 rows37 *
    Thompson.BinaryMatrix.decode 78 rows36 = Thompson.BinaryMatrix.decode 78 rows38 :=
  Thompson.BinaryMatrix.decode_mul 78 rows37 rows36 rows38 product49_check

private theorem product50_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows17[i.val]! (generatorRows 2) 78 = rows39[i.val]! := by
  decide +kernel

theorem product50 : Thompson.BinaryMatrix.decode 78 rows17 *
    Thompson.BinaryMatrix.decode 78 (generatorRows 2) = Thompson.BinaryMatrix.decode 78 rows39 :=
  Thompson.BinaryMatrix.decode_mul 78 rows17 (generatorRows 2) rows39 product50_check

private theorem product51_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows39[i.val]! rows17 78 = rows40[i.val]! := by
  decide +kernel

theorem product51 : Thompson.BinaryMatrix.decode 78 rows39 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows40 :=
  Thompson.BinaryMatrix.decode_mul 78 rows39 rows17 rows40 product51_check

private theorem product52_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows40[i.val]! (generatorRows 2) 78 = rows41[i.val]! := by
  decide +kernel

theorem product52 : Thompson.BinaryMatrix.decode 78 rows40 *
    Thompson.BinaryMatrix.decode 78 (generatorRows 2) = Thompson.BinaryMatrix.decode 78 rows41 :=
  Thompson.BinaryMatrix.decode_mul 78 rows40 (generatorRows 2) rows41 product52_check

private theorem product53_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows41[i.val]! rows17 78 = rows42[i.val]! := by
  decide +kernel

theorem product53 : Thompson.BinaryMatrix.decode 78 rows41 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows42 :=
  Thompson.BinaryMatrix.decode_mul 78 rows41 rows17 rows42 product53_check

private theorem product54_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows42[i.val]! rows43 78 = 2 ^ i.val := by
  decide +kernel

theorem product54 : Thompson.BinaryMatrix.decode 78 rows42 *
    Thompson.BinaryMatrix.decode 78 rows43 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows42 rows43 product54_check

private theorem product55_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows17[i.val]! rows17 78 = rows44[i.val]! := by
  decide +kernel

theorem product55 : Thompson.BinaryMatrix.decode 78 rows17 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows44 :=
  Thompson.BinaryMatrix.decode_mul 78 rows17 rows17 rows44 product55_check

private theorem product56_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows35[i.val]! rows35 78 = rows45[i.val]! := by
  decide +kernel

theorem product56 : Thompson.BinaryMatrix.decode 78 rows35 *
    Thompson.BinaryMatrix.decode 78 rows35 = Thompson.BinaryMatrix.decode 78 rows45 :=
  Thompson.BinaryMatrix.decode_mul 78 rows35 rows35 rows45 product56_check

private theorem product57_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! (generatorRows 2) 78 = 2 ^ i.val := by
  decide +kernel

theorem product57 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 (generatorRows 2) = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 (generatorRows 2) (generatorRows 2) product57_check

private theorem product58_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows17[i.val]! rows17 78 = rows44[i.val]! := by
  decide +kernel

theorem product58 : Thompson.BinaryMatrix.decode 78 rows17 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows44 :=
  Thompson.BinaryMatrix.decode_mul 78 rows17 rows17 rows44 product58_check

private theorem product59_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows44[i.val]! rows17 78 = rows46[i.val]! := by
  decide +kernel

theorem product59 : Thompson.BinaryMatrix.decode 78 rows44 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows46 :=
  Thompson.BinaryMatrix.decode_mul 78 rows44 rows17 rows46 product59_check

private theorem product60_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows46[i.val]! rows17 78 = rows47[i.val]! := by
  decide +kernel

theorem product60 : Thompson.BinaryMatrix.decode 78 rows46 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows47 :=
  Thompson.BinaryMatrix.decode_mul 78 rows46 rows17 rows47 product60_check

private theorem product61_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows47[i.val]! rows17 78 = rows45[i.val]! := by
  decide +kernel

theorem product61 : Thompson.BinaryMatrix.decode 78 rows47 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows45 :=
  Thompson.BinaryMatrix.decode_mul 78 rows47 rows17 rows45 product61_check

private theorem product62_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows45[i.val]! rows17 78 = rows35[i.val]! := by
  decide +kernel

theorem product62 : Thompson.BinaryMatrix.decode 78 rows45 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows35 :=
  Thompson.BinaryMatrix.decode_mul 78 rows45 rows17 rows35 product62_check

private theorem product63_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows35[i.val]! rows17 78 = 2 ^ i.val := by
  decide +kernel

theorem product63 : Thompson.BinaryMatrix.decode 78 rows35 *
    Thompson.BinaryMatrix.decode 78 rows17 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows35 rows17 product63_check

end Theory.SpecificGroups.LieType.SourceLevi.E6.WordCertificates.Checked
