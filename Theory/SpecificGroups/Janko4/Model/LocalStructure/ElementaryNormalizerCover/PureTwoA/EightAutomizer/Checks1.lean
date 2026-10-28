module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Checks0
/-! Kernel-checked native products, bounded sequential batch 1. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_inverse_ci : packedMul cRows ciRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
theorem check_inverse_n0i : packedMul Janko4.LocalStructure.LinearFive.NativeNormalizer.n0Rows n0iRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
theorem check_inverse_n1i : packedMul Janko4.LocalStructure.LinearFive.NativeNormalizer.n1Rows n1iRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by simp only [packedOne, get_ofFn]; decide +kernel)
theorem check_cu0 : packedMul cRows Janko4.LocalStructure.LinearFive.NativeNormalizer.n0Rows = cu0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_actor0 : packedMul cu0Rows ciRows = actor0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u1_0 : packedMul n1iRows n1iRows = u1_0Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u1_1 : packedMul u1_0Rows n1iRows = u1_1Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_u1_2 : packedMul u1_1Rows Janko4.LocalStructure.LinearFive.NativeNormalizer.n0Rows = u1_2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
