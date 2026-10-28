module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks4
/-! Kernel-checked native products, bounded sequential batch 5. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_m183 : packedMul m55Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m183Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m11 : packedMul m3Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = m11Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m27 : packedMul m11Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m27Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m59 : packedMul m27Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m59Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m187 : packedMul m59Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m187Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m5 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) = m5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m37 : packedMul m5Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m37Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m19 : packedMul m3Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m19Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
