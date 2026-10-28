module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks3
/-! Kernel-checked native products, bounded sequential batch 4. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_m52 : packedMul m20Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m52Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m17 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m17Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m49 : packedMul m17Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m49Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m177 : packedMul m49Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m177Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m3 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) = m3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m7 : packedMul m3Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) = m7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m23 : packedMul m7Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m23Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m55 : packedMul m23Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m55Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
