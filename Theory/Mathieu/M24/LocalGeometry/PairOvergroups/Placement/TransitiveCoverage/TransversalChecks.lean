module
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalChecks.Part0
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalChecks.Part1
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalChecks.Part2
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalChecks.Part3
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage.TransversalChecks.Part4

/-!
# Checked strict increase of all 239,085 native Sylow coset keys

Every adjacent pair is checked in one of 45 independent blocks. Combining
the blocks certifies injectivity into native cosets, the input used by the
cardinality argument in `Coverage`.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage

theorem keyBlock_checks (a : Fin 45) : KeyBlock a.val := by
  fin_cases a
  · exact keyBlock_00
  · exact keyBlock_01
  · exact keyBlock_02
  · exact keyBlock_03
  · exact keyBlock_04
  · exact keyBlock_05
  · exact keyBlock_06
  · exact keyBlock_07
  · exact keyBlock_08
  · exact keyBlock_09
  · exact keyBlock_10
  · exact keyBlock_11
  · exact keyBlock_12
  · exact keyBlock_13
  · exact keyBlock_14
  · exact keyBlock_15
  · exact keyBlock_16
  · exact keyBlock_17
  · exact keyBlock_18
  · exact keyBlock_19
  · exact keyBlock_20
  · exact keyBlock_21
  · exact keyBlock_22
  · exact keyBlock_23
  · exact keyBlock_24
  · exact keyBlock_25
  · exact keyBlock_26
  · exact keyBlock_27
  · exact keyBlock_28
  · exact keyBlock_29
  · exact keyBlock_30
  · exact keyBlock_31
  · exact keyBlock_32
  · exact keyBlock_33
  · exact keyBlock_34
  · exact keyBlock_35
  · exact keyBlock_36
  · exact keyBlock_37
  · exact keyBlock_38
  · exact keyBlock_39
  · exact keyBlock_40
  · exact keyBlock_41
  · exact keyBlock_42
  · exact keyBlock_43
  · exact keyBlock_44

end Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
