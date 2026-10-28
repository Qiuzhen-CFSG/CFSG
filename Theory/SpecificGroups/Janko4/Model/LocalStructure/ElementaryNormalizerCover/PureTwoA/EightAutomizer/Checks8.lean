module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks7
/-! Kernel-checked native products, bounded sequential batch 8. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_m13 : packedMul m5Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = m13Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m29 : packedMul m13Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m29Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m36 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m36Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m100 : packedMul m36Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = m100Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m228 : packedMul m100Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m228Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m61 : packedMul m29Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m61Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m189 : packedMul m61Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m189Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m101 : packedMul m37Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = m101Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
