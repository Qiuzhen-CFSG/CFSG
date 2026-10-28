module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockChecks0
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockChecks1
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockChecks2
public import Theory.SpecificGroups.Janko3.Model.Order.Level0.ForwardB.SeedsLow.BlockChecks3
import Mathlib.Tactic.FinCases

/-! The checked four-letter products, assembled as an evaluator specification.
Source and construction: BlockData. -/

namespace Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
open Theory.GroupTheory
set_option Elab.async false

public theorem rawBlock_spec (i : Fin 76) (x : Fin 6156) :
    rawBlock i x.val = (evalWord gen (blockWord i) x).val := by
  fin_cases i
  · exact block0_spec x
  · exact block1_spec x
  · exact block2_spec x
  · exact block3_spec x
  · exact block4_spec x
  · exact block5_spec x
  · exact block6_spec x
  · exact block7_spec x
  · exact block8_spec x
  · exact block9_spec x
  · exact block10_spec x
  · exact block11_spec x
  · exact block12_spec x
  · exact block13_spec x
  · exact block14_spec x
  · exact block15_spec x
  · exact block16_spec x
  · exact block17_spec x
  · exact block18_spec x
  · exact block19_spec x
  · exact block20_spec x
  · exact block21_spec x
  · exact block22_spec x
  · exact block23_spec x
  · exact block24_spec x
  · exact block25_spec x
  · exact block26_spec x
  · exact block27_spec x
  · exact block28_spec x
  · exact block29_spec x
  · exact block30_spec x
  · exact block31_spec x
  · exact block32_spec x
  · exact block33_spec x
  · exact block34_spec x
  · exact block35_spec x
  · exact block36_spec x
  · exact block37_spec x
  · exact block38_spec x
  · exact block39_spec x
  · exact block40_spec x
  · exact block41_spec x
  · exact block42_spec x
  · exact block43_spec x
  · exact block44_spec x
  · exact block45_spec x
  · exact block46_spec x
  · exact block47_spec x
  · exact block48_spec x
  · exact block49_spec x
  · exact block50_spec x
  · exact block51_spec x
  · exact block52_spec x
  · exact block53_spec x
  · exact block54_spec x
  · exact block55_spec x
  · exact block56_spec x
  · exact block57_spec x
  · exact block58_spec x
  · exact block59_spec x
  · exact block60_spec x
  · exact block61_spec x
  · exact block62_spec x
  · exact block63_spec x
  · exact block64_spec x
  · exact block65_spec x
  · exact block66_spec x
  · exact block67_spec x
  · exact block68_spec x
  · exact block69_spec x
  · exact block70_spec x
  · exact block71_spec x
  · exact block72_spec x
  · exact block73_spec x
  · exact block74_spec x
  · exact block75_spec x

end Sporadic.Janko3.OrderCertificate.Level0.ForwardB.SeedsLow
