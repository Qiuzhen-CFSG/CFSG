module

public import Theory.SpecificGroups.LieType.A02ParabolicSections.SourceLevi.E6.WordCertificates.Arithmetic3

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

private theorem product64_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows17 78 = rows48[i.val]! := by
  decide +kernel

theorem product64 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows17 = Thompson.BinaryMatrix.decode 78 rows48 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows17 rows48 product64_check

private theorem product65_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows48[i.val]! rows48 78 = rows49[i.val]! := by
  decide +kernel

theorem product65 : Thompson.BinaryMatrix.decode 78 rows48 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows49 :=
  Thompson.BinaryMatrix.decode_mul 78 rows48 rows48 rows49 product65_check

private theorem product66_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows49[i.val]! rows48 78 = rows50[i.val]! := by
  decide +kernel

theorem product66 : Thompson.BinaryMatrix.decode 78 rows49 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows50 :=
  Thompson.BinaryMatrix.decode_mul 78 rows49 rows48 rows50 product66_check

private theorem product67_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows50[i.val]! rows48 78 = rows51[i.val]! := by
  decide +kernel

theorem product67 : Thompson.BinaryMatrix.decode 78 rows50 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows51 :=
  Thompson.BinaryMatrix.decode_mul 78 rows50 rows48 rows51 product67_check

private theorem product68_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows51[i.val]! rows48 78 = rows52[i.val]! := by
  decide +kernel

theorem product68 : Thompson.BinaryMatrix.decode 78 rows51 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows52 :=
  Thompson.BinaryMatrix.decode_mul 78 rows51 rows48 rows52 product68_check

private theorem product69_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows52[i.val]! rows48 78 = rows53[i.val]! := by
  decide +kernel

theorem product69 : Thompson.BinaryMatrix.decode 78 rows52 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows53 :=
  Thompson.BinaryMatrix.decode_mul 78 rows52 rows48 rows53 product69_check

private theorem product70_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows53[i.val]! rows48 78 = rows54[i.val]! := by
  decide +kernel

theorem product70 : Thompson.BinaryMatrix.decode 78 rows53 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows54 :=
  Thompson.BinaryMatrix.decode_mul 78 rows53 rows48 rows54 product70_check

private theorem product71_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows54[i.val]! rows48 78 = rows55[i.val]! := by
  decide +kernel

theorem product71 : Thompson.BinaryMatrix.decode 78 rows54 *
    Thompson.BinaryMatrix.decode 78 rows48 = Thompson.BinaryMatrix.decode 78 rows55 :=
  Thompson.BinaryMatrix.decode_mul 78 rows54 rows48 rows55 product71_check

private theorem product72_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows55[i.val]! rows48 78 = 2 ^ i.val := by
  decide +kernel

theorem product72 : Thompson.BinaryMatrix.decode 78 rows55 *
    Thompson.BinaryMatrix.decode 78 rows48 = 1 :=
  Thompson.BinaryMatrix.decode_mul_one 78 rows55 rows48 product72_check

private theorem product73_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct (generatorRows 2)[i.val]! rows44 78 = rows56[i.val]! := by
  decide +kernel

theorem product73 : Thompson.BinaryMatrix.decode 78 (generatorRows 2) *
    Thompson.BinaryMatrix.decode 78 rows44 = Thompson.BinaryMatrix.decode 78 rows56 :=
  Thompson.BinaryMatrix.decode_mul 78 (generatorRows 2) rows44 rows56 product73_check

private theorem product74_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows56[i.val]! rows56 78 = rows57[i.val]! := by
  decide +kernel

theorem product74 : Thompson.BinaryMatrix.decode 78 rows56 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows57 :=
  Thompson.BinaryMatrix.decode_mul 78 rows56 rows56 rows57 product74_check

private theorem product75_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows57[i.val]! rows56 78 = rows58[i.val]! := by
  decide +kernel

theorem product75 : Thompson.BinaryMatrix.decode 78 rows57 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows58 :=
  Thompson.BinaryMatrix.decode_mul 78 rows57 rows56 rows58 product75_check

private theorem product76_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows58[i.val]! rows56 78 = rows59[i.val]! := by
  decide +kernel

theorem product76 : Thompson.BinaryMatrix.decode 78 rows58 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows59 :=
  Thompson.BinaryMatrix.decode_mul 78 rows58 rows56 rows59 product76_check

private theorem product77_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows59[i.val]! rows56 78 = rows60[i.val]! := by
  decide +kernel

theorem product77 : Thompson.BinaryMatrix.decode 78 rows59 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows60 :=
  Thompson.BinaryMatrix.decode_mul 78 rows59 rows56 rows60 product77_check

private theorem product78_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows60[i.val]! rows56 78 = rows61[i.val]! := by
  decide +kernel

theorem product78 : Thompson.BinaryMatrix.decode 78 rows60 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows61 :=
  Thompson.BinaryMatrix.decode_mul 78 rows60 rows56 rows61 product78_check

private theorem product79_check : ∀ i : Fin 78,
    Thompson.BinaryMatrix.rowProduct rows61[i.val]! rows56 78 = rows62[i.val]! := by
  decide +kernel

theorem product79 : Thompson.BinaryMatrix.decode 78 rows61 *
    Thompson.BinaryMatrix.decode 78 rows56 = Thompson.BinaryMatrix.decode 78 rows62 :=
  Thompson.BinaryMatrix.decode_mul 78 rows61 rows56 rows62 product79_check

end Theory.SpecificGroups.LieType.SourceLevi.E6.WordCertificates.Checked
