module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.WordCertificates.Arithmetic4

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

private theorem product80_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows62[i.val]! rows56 52 = rows63[i.val]! := by
  decide +kernel

theorem product80 : Thompson.BinaryMatrix.decode 52 rows62 *
    Thompson.BinaryMatrix.decode 52 rows56 = Thompson.BinaryMatrix.decode 52 rows63 :=
  Thompson.BinaryMatrix.decode_mul 52 rows62 rows56 rows63 product80_check

private theorem product81_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows63[i.val]! rows56 52 = rows64[i.val]! := by
  decide +kernel

theorem product81 : Thompson.BinaryMatrix.decode 52 rows63 *
    Thompson.BinaryMatrix.decode 52 rows56 = Thompson.BinaryMatrix.decode 52 rows64 :=
  Thompson.BinaryMatrix.decode_mul 52 rows63 rows56 rows64 product81_check

private theorem product82_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows64[i.val]! rows56 52 = rows65[i.val]! := by
  decide +kernel

theorem product82 : Thompson.BinaryMatrix.decode 52 rows64 *
    Thompson.BinaryMatrix.decode 52 rows56 = Thompson.BinaryMatrix.decode 52 rows65 :=
  Thompson.BinaryMatrix.decode_mul 52 rows64 rows56 rows65 product82_check

private theorem product83_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows65[i.val]! rows56 52 = rows66[i.val]! := by
  decide +kernel

theorem product83 : Thompson.BinaryMatrix.decode 52 rows65 *
    Thompson.BinaryMatrix.decode 52 rows56 = Thompson.BinaryMatrix.decode 52 rows66 :=
  Thompson.BinaryMatrix.decode_mul 52 rows65 rows56 rows66 product83_check

private theorem product84_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows66[i.val]! rows56 52 = 2 ^ i.val := by
  decide +kernel

theorem product84 : Thompson.BinaryMatrix.decode 52 rows66 *
    Thompson.BinaryMatrix.decode 52 rows56 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 rows66 rows56 product84_check

private theorem product85_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows43 52 = rows67[i.val]! := by
  decide +kernel

theorem product85 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows43 = Thompson.BinaryMatrix.decode 52 rows67 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows43 rows67 product85_check

private theorem product86_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows67[i.val]! (generatorRows 2) 52 = rows68[i.val]! := by
  decide +kernel

theorem product86 : Thompson.BinaryMatrix.decode 52 rows67 *
    Thompson.BinaryMatrix.decode 52 (generatorRows 2) = Thompson.BinaryMatrix.decode 52 rows68 :=
  Thompson.BinaryMatrix.decode_mul 52 rows67 (generatorRows 2) rows68 product86_check

private theorem product87_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows68[i.val]! rows42 52 = rows69[i.val]! := by
  decide +kernel

theorem product87 : Thompson.BinaryMatrix.decode 52 rows68 *
    Thompson.BinaryMatrix.decode 52 rows42 = Thompson.BinaryMatrix.decode 52 rows69 :=
  Thompson.BinaryMatrix.decode_mul 52 rows68 rows42 rows69 product87_check

private theorem product88_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows69[i.val]! rows69 52 = 2 ^ i.val := by
  decide +kernel

theorem product88 : Thompson.BinaryMatrix.decode 52 rows69 *
    Thompson.BinaryMatrix.decode 52 rows69 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 rows69 rows69 product88_check

private theorem product89_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows35 52 = rows70[i.val]! := by
  decide +kernel

theorem product89 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows35 = Thompson.BinaryMatrix.decode 52 rows70 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows35 rows70 product89_check

private theorem product90_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows70[i.val]! (generatorRows 2) 52 = rows71[i.val]! := by
  decide +kernel

theorem product90 : Thompson.BinaryMatrix.decode 52 rows70 *
    Thompson.BinaryMatrix.decode 52 (generatorRows 2) = Thompson.BinaryMatrix.decode 52 rows71 :=
  Thompson.BinaryMatrix.decode_mul 52 rows70 (generatorRows 2) rows71 product90_check

private theorem product91_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows71[i.val]! rows17 52 = rows72[i.val]! := by
  decide +kernel

theorem product91 : Thompson.BinaryMatrix.decode 52 rows71 *
    Thompson.BinaryMatrix.decode 52 rows17 = Thompson.BinaryMatrix.decode 52 rows72 :=
  Thompson.BinaryMatrix.decode_mul 52 rows71 rows17 rows72 product91_check

private theorem product92_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows72[i.val]! rows72 52 = rows73[i.val]! := by
  decide +kernel

theorem product92 : Thompson.BinaryMatrix.decode 52 rows72 *
    Thompson.BinaryMatrix.decode 52 rows72 = Thompson.BinaryMatrix.decode 52 rows73 :=
  Thompson.BinaryMatrix.decode_mul 52 rows72 rows72 rows73 product92_check

private theorem product93_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows73[i.val]! rows72 52 = 2 ^ i.val := by
  decide +kernel

theorem product93 : Thompson.BinaryMatrix.decode 52 rows73 *
    Thompson.BinaryMatrix.decode 52 rows72 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 rows73 rows72 product93_check

private theorem product94_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows45 52 = rows74[i.val]! := by
  decide +kernel

theorem product94 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows45 = Thompson.BinaryMatrix.decode 52 rows74 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows45 rows74 product94_check

private theorem product95_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows74[i.val]! (generatorRows 2) 52 = rows75[i.val]! := by
  decide +kernel

theorem product95 : Thompson.BinaryMatrix.decode 52 rows74 *
    Thompson.BinaryMatrix.decode 52 (generatorRows 2) = Thompson.BinaryMatrix.decode 52 rows75 :=
  Thompson.BinaryMatrix.decode_mul 52 rows74 (generatorRows 2) rows75 product95_check

end Theory.SpecificGroups.LieType.SourceLevi.F4.WordCertificates.Checked
