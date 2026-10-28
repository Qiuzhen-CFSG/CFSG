module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks2
/-! Kernel-checked native products, bounded sequential batch 3. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_u2_3 : packedMul u2_2Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows = u2_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_4 : packedMul u2_3Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n0Rows = u2_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_5 : packedMul u2_4Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows = u2_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_6 : packedMul u2_5Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n0Rows = u2_6Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_7 : packedMul u2_6Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows = u2_7Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_cu2 : packedMul cRows u2_7Rows = cu2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_actor2 : packedMul cu2Rows ciRows = actor2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_m20 : packedMul (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 2) (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 4) = m20Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
