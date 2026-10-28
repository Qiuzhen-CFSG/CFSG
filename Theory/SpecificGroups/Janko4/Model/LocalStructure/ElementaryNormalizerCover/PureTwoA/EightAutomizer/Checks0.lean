module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Rows
/-! Kernel-checked native products, bounded sequential batch 0. -/
public section
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
open Janko4.GeneratorCertificates
set_option maxRecDepth 10000
set_option Elab.async false
theorem check_xy : packedMul Janko4.Cardinality.KernelCount.xRows Janko4.Cardinality.KernelCount.yRows = xyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_xyy : packedMul xyRows Janko4.Cardinality.KernelCount.yRows = xyyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_p2 : packedMul xyyRows xyyRows = p2Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_p4 : packedMul p2Rows p2Rows = p4Rows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_cx : packedMul p4Rows Janko4.Cardinality.KernelCount.xRows = cxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_cxy : packedMul cxRows Janko4.Cardinality.KernelCount.yRows = cxyRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_cxyx : packedMul cxyRows Janko4.Cardinality.KernelCount.xRows = cxyxRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
theorem check_c : packedMul cxyxRows (Janko4.LocalStructure.ElementaryEightGeometry.Loewy.generatorRows 0) = cRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)
end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.EightAutomizer.Native
