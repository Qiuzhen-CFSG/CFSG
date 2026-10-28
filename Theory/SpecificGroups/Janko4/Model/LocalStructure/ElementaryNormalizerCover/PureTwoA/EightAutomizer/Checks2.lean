module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks1
/-! Kernel-checked native products, bounded sequential batch 2. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_u1_3 : packedMul u1_2Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows = u1_3Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u1_4 : packedMul u1_3Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows = u1_4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u1_5 : packedMul u1_4Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows = u1_5Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_cu1 : packedMul cRows u1_5Rows = cu1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_actor1 : packedMul cu1Rows ciRows = actor1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_0 : packedMul n1iRows n0iRows = u2_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_1 : packedMul u2_0Rows n1iRows = u2_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u2_2 : packedMul u2_1Rows n0iRows = u2_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
