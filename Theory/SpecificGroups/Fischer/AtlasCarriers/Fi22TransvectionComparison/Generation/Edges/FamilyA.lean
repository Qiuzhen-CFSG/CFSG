module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A00
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A01
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A02
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A03
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A04
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A05
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A06
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A07
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A08
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A09
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A10
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A12
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.A13

/-!
# Certified Fi22 A Schreier edges

The bounded checks cover all 3510 labels. Tree edges cancel algebraically;
all remaining edges agree on the faithful 48 coordinates with products of
certified subgroup elements. This discharges the A family of the literal
edge premise in the commuting-conjugate generation argument.

Source: ATLAS F22G1-p3510B0; the conjugation-action paragraph after GLS3 Table 5.3t.
Reproduce the certificates with `source/generate.py --check`.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

private theorem allChecks : BitNetwork.check (edgeCheck false) 0 3510 = true :=
  (BitNetwork.check_append (edgeCheck false) 0 256 3254
    checkedA00 (BitNetwork.check_append (edgeCheck false) 256 256 2998
    checkedA01 (BitNetwork.check_append (edgeCheck false) 512 256 2742
    checkedA02 (BitNetwork.check_append (edgeCheck false) 768 256 2486
    checkedA03 (BitNetwork.check_append (edgeCheck false) 1024 256 2230
    checkedA04 (BitNetwork.check_append (edgeCheck false) 1280 256 1974
    checkedA05 (BitNetwork.check_append (edgeCheck false) 1536 256 1718
    checkedA06 (BitNetwork.check_append (edgeCheck false) 1792 256 1462
    checkedA07 (BitNetwork.check_append (edgeCheck false) 2048 256 1206
    checkedA08 (BitNetwork.check_append (edgeCheck false) 2304 256 950
    checkedA09 (BitNetwork.check_append (edgeCheck false) 2560 256 694
    checkedA10 (BitNetwork.check_append (edgeCheck false) 2816 256 438
    checkedA11 (BitNetwork.check_append (edgeCheck false) 3072 256 182
    checkedA12 checkedA13)))))))))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges

public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison

/-- All literal Schreier edges for the ATLAS generator A lie in the commuting-conjugate subgroup. -/
theorem atlasA_schreierEdge_mem (x : Fin 3510) :
    (pointTransport (inclusion atlasA x))⁻¹ * atlasA * pointTransport x ∈
      commutingConjugateSubgroup :=
  Generation.Edges.edgeCheck_mem false Generation.Edges.allChecks x

end Sporadic.Fischer.Fi22.TransvectionComparison
