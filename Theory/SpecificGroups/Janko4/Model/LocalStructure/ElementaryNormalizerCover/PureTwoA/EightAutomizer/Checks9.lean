module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks8
/-! Kernel-checked native products, bounded sequential batch 9. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_m74 : packedMul m10Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = m74Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_ag : packedMul Janko4.aRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = agRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_ag2 : packedMul agRows agRows = ag2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_ag4 : packedMul ag2Rows ag2Rows = ag4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_ag8 : packedMul ag4Rows ag4Rows = ag8Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_ag10 : packedMul ag8Rows ag2Rows = ag10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_eleven : packedMul ag10Rows agRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
theorem conjugates_0_0 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) = packedMul m52Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
