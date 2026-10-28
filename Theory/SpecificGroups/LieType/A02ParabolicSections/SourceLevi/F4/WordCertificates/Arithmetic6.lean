module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.F4.WordCertificates.Arithmetic5

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

private theorem product96_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows75[i.val]! rows44 52 = rows76[i.val]! := by
  decide +kernel

theorem product96 : Thompson.BinaryMatrix.decode 52 rows75 *
    Thompson.BinaryMatrix.decode 52 rows44 = Thompson.BinaryMatrix.decode 52 rows76 :=
  Thompson.BinaryMatrix.decode_mul 52 rows75 rows44 rows76 product96_check

private theorem product97_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows76[i.val]! rows76 52 = 2 ^ i.val := by
  decide +kernel

theorem product97 : Thompson.BinaryMatrix.decode 52 rows76 *
    Thompson.BinaryMatrix.decode 52 rows76 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 52 rows76 rows76 product97_check

private theorem product98_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows38 52 = rows77[i.val]! := by
  decide +kernel

theorem product98 : Thompson.BinaryMatrix.decode 52 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 52 rows38 = Thompson.BinaryMatrix.decode 52 rows77 :=
  Thompson.BinaryMatrix.decode_mul 52 (generatorRows 2) rows38 rows77 product98_check

private theorem product99_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows38[i.val]! (generatorRows 2) 52 = rows77[i.val]! := by
  decide +kernel

theorem product99 : Thompson.BinaryMatrix.decode 52 rows38 *
    Thompson.BinaryMatrix.decode 52 (generatorRows 2) = Thompson.BinaryMatrix.decode 52 rows77 :=
  Thompson.BinaryMatrix.decode_mul 52 rows38 (generatorRows 2) rows77 product99_check

private theorem product100_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows17[i.val]! rows38 52 = rows78[i.val]! := by
  decide +kernel

theorem product100 : Thompson.BinaryMatrix.decode 52 rows17 *
    Thompson.BinaryMatrix.decode 52 rows38 = Thompson.BinaryMatrix.decode 52 rows78 :=
  Thompson.BinaryMatrix.decode_mul 52 rows17 rows38 rows78 product100_check

private theorem product101_check : ∀ i : Fin 52,
    Thompson.BinaryMatrix.rowProduct rows38[i.val]! rows17 52 = rows78[i.val]! := by
  decide +kernel

theorem product101 : Thompson.BinaryMatrix.decode 52 rows38 *
    Thompson.BinaryMatrix.decode 52 rows17 = Thompson.BinaryMatrix.decode 52 rows78 :=
  Thompson.BinaryMatrix.decode_mul 52 rows38 rows17 rows78 product101_check

end Theory.SpecificGroups.LieType.SourceLevi.F4.WordCertificates.Checked
