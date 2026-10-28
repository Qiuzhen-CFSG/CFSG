module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks6
/-! Kernel-checked native products, bounded sequential batch 7. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_m10 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = m10Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m26 : packedMul m10Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m26Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m58 : packedMul m26Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m58Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m186 : packedMul m58Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m186Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m48 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m48Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m176 : packedMul m48Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m176Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m6 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 1) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) = m6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m22 : packedMul m6Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m22Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
