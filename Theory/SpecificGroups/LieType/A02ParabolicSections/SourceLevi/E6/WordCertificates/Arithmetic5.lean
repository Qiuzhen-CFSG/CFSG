module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.WordCertificates.Arithmetic4

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

private theorem product80_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows62[i.val]! rows56 78 = rows63[i.val]! := by
  decide +kernel

theorem product80 : Thompson.BinaryMatrix.decode 78 rows62 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows63 :=
  Thompson.BinaryMatrix.decode_mul 78 rows62 rows56 rows63 product80_check

private theorem product81_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows63[i.val]! rows56 78 = rows64[i.val]! := by
  decide +kernel

theorem product81 : Thompson.BinaryMatrix.decode 78 rows63 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows64 :=
  Thompson.BinaryMatrix.decode_mul 78 rows63 rows56 rows64 product81_check

private theorem product82_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows64[i.val]! rows56 78 = rows65[i.val]! := by
  decide +kernel

theorem product82 : Thompson.BinaryMatrix.decode 78 rows64 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows65 :=
  Thompson.BinaryMatrix.decode_mul 78 rows64 rows56 rows65 product82_check

private theorem product83_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows65[i.val]! rows56 78 = rows66[i.val]! := by
  decide +kernel

theorem product83 : Thompson.BinaryMatrix.decode 78 rows65 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows66 :=
  Thompson.BinaryMatrix.decode_mul 78 rows65 rows56 rows66 product83_check

private theorem product84_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows66[i.val]! rows56 78 = 2 ^ i.val := by
  decide +kernel

theorem product84 : Thompson.BinaryMatrix.decode 78 rows66 *
    Thompson.BinaryMatrix.decode 78 rows56 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows66 rows56 product84_check

private theorem product85_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows43 78 = rows67[i.val]! := by
  decide +kernel

theorem product85 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows43 = Thompson.BinaryMatrix.decode 78 rows67 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows43 rows67 product85_check

private theorem product86_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows67[i.val]! (generatorRows 2) 78 = rows68[i.val]! := by
  decide +kernel

theorem product86 : Thompson.BinaryMatrix.decode 78 rows67 *
    Thompson.BinaryMatrix.decode 78 (generatorRows 2) = Thompson.BinaryMatrix.decode 78 rows68 :=
  Thompson.BinaryMatrix.decode_mul 78 rows67 (generatorRows 2) rows68 product86_check

private theorem product87_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows68[i.val]! rows42 78 = rows69[i.val]! := by
  decide +kernel

theorem product87 : Thompson.BinaryMatrix.decode 78 rows68 *
    Thompson.BinaryMatrix.decode 78 rows42 = Thompson.BinaryMatrix.decode 78 rows69 :=
  Thompson.BinaryMatrix.decode_mul 78 rows68 rows42 rows69 product87_check

private theorem product88_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows69[i.val]! rows69 78 = 2 ^ i.val := by
  decide +kernel

theorem product88 : Thompson.BinaryMatrix.decode 78 rows69 *
    Thompson.BinaryMatrix.decode 78 rows69 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows69 rows69 product88_check

private theorem product89_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows35 78 = rows70[i.val]! := by
  decide +kernel

theorem product89 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows35 = Thompson.BinaryMatrix.decode 78 rows70 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows35 rows70 product89_check

private theorem product90_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows70[i.val]! (generatorRows 2) 78 = rows71[i.val]! := by
  decide +kernel

theorem product90 : Thompson.BinaryMatrix.decode 78 rows70 *
    Thompson.BinaryMatrix.decode 78 (generatorRows 2) = Thompson.BinaryMatrix.decode 78 rows71 :=
  Thompson.BinaryMatrix.decode_mul 78 rows70 (generatorRows 2) rows71 product90_check

private theorem product91_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows71[i.val]! rows17 78 = rows72[i.val]! := by
  decide +kernel

theorem product91 : Thompson.BinaryMatrix.decode 78 rows71 *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows72 :=
  Thompson.BinaryMatrix.decode_mul 78 rows71 rows17 rows72 product91_check

private theorem product92_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows72[i.val]! rows72 78 = rows73[i.val]! := by
  decide +kernel

theorem product92 : Thompson.BinaryMatrix.decode 78 rows72 *
    Thompson.BinaryMatrix.decode 78 rows72 = Thompson.BinaryMatrix.decode 78 rows73 :=
  Thompson.BinaryMatrix.decode_mul 78 rows72 rows72 rows73 product92_check

private theorem product93_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows73[i.val]! rows72 78 = 2 ^ i.val := by
  decide +kernel

theorem product93 : Thompson.BinaryMatrix.decode 78 rows73 *
    Thompson.BinaryMatrix.decode 78 rows72 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows73 rows72 product93_check

private theorem product94_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows45 78 = rows74[i.val]! := by
  decide +kernel

theorem product94 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows45 = Thompson.BinaryMatrix.decode 78 rows74 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows45 rows74 product94_check

private theorem product95_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows74[i.val]! (generatorRows 2) 78 = rows75[i.val]! := by
  decide +kernel

theorem product95 : Thompson.BinaryMatrix.decode 78 rows74 *
    Thompson.BinaryMatrix.decode 78 (generatorRows 2) = Thompson.BinaryMatrix.decode 78 rows75 :=
  Thompson.BinaryMatrix.decode_mul 78 rows74 (generatorRows 2) rows75 product95_check

end Theory.SpecificGroups.LieType.SourceLevi.E6.WordCertificates.Checked
