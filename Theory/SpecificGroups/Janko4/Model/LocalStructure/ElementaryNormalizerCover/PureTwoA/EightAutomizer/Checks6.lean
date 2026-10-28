module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks5
/-! Kernel-checked native products, bounded sequential batch 6. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_m147 : packedMul m19Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m147Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m51 : packedMul m19Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m51Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m115 : packedMul m51Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 6) = m115Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m243 : packedMul m115Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m243Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m12 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 3) = m12Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m28 : packedMul m12Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m28Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m60 : packedMul m28Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 5) = m60Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m188 : packedMul m60Rows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 7) = m188Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
