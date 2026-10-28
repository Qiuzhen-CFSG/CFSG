module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks10
/-! Kernel-checked native products, bounded sequential batch 11. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem conjugates_1_1 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) = packedMul m188Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_2 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) = packedMul m186Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_3 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = packedMul m176Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_4 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = packedMul m22Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_5 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = packedMul m29Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_6 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = packedMul m228Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_1_7 : packedMul actor1Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = packedMul m3Rows actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
theorem conjugates_2_0 : packedMul actor2Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) = packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedMul, get_ofFn]; decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
