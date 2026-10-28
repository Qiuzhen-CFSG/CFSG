module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks11
/-! Kernel-checked native products, bounded sequential batch 12. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem conjugates_2_1 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) = packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_2 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) = packedMul m13Rows actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_3 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_4 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = packedMul m189Rows actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_5 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = packedMul m101Rows actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_6 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = packedMul m74Rows actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_7 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
