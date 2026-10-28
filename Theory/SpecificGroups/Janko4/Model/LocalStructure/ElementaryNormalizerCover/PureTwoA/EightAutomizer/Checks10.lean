module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks9
/-! Kernel-checked native products, bounded sequential batch 10. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem conjugates_0_1 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) = packedMul m177Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_0_2 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) = packedMul m183Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_0_3 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = packedMul m187Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_0_4 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = packedMul m37Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_0_5 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = packedMul m147Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_0_6 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = packedMul m243Rows actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_0_7 : packedMul actor0Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_0 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) = packedMul m60Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
