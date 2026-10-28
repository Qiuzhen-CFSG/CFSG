module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B00
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B01
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B02
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B03
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B04
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B05
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B06
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B07
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B08
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B09
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B10
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B12
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Blocks.B13

/-!
# Certified Fi22 B Schreier edges

The bounded checks cover all 3510 labels. Tree edges cancel algebraically;
all remaining edges agree on the faithful 48 coordinates with products of
certified subgroup elements. This discharges the B family of the literal
edge premise in the commuting-conjugate generation argument.

Source: ATLAS F22G1-p3510B0; the conjugation-action paragraph after GLS3 Table 5.3t.
Reproduce the certificates with `source/generate.py --check`.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

private theorem allChecks : BitNetwork.check (edgeCheck true) 0 3510 = true :=
  (BitNetwork.check_append (edgeCheck true) 0 256 3254
    checkedB00 (BitNetwork.check_append (edgeCheck true) 256 256 2998
    checkedB01 (BitNetwork.check_append (edgeCheck true) 512 256 2742
    checkedB02 (BitNetwork.check_append (edgeCheck true) 768 256 2486
    checkedB03 (BitNetwork.check_append (edgeCheck true) 1024 256 2230
    checkedB04 (BitNetwork.check_append (edgeCheck true) 1280 256 1974
    checkedB05 (BitNetwork.check_append (edgeCheck true) 1536 256 1718
    checkedB06 (BitNetwork.check_append (edgeCheck true) 1792 256 1462
    checkedB07 (BitNetwork.check_append (edgeCheck true) 2048 256 1206
    checkedB08 (BitNetwork.check_append (edgeCheck true) 2304 256 950
    checkedB09 (BitNetwork.check_append (edgeCheck true) 2560 256 694
    checkedB10 (BitNetwork.check_append (edgeCheck true) 2816 256 438
    checkedB11 (BitNetwork.check_append (edgeCheck true) 3072 256 182
    checkedB12 checkedB13)))))))))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges

public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison

/-- All literal Schreier edges for the ATLAS generator B lie in the commuting-conjugate subgroup. -/
theorem atlasB_schreierEdge_mem (x : Fin 3510) :
    (pointTransport (inclusion atlasB x))⁻¹ * atlasB * pointTransport x ∈
      commutingConjugateSubgroup :=
  Generation.Edges.edgeCheck_mem true Generation.Edges.allChecks x

end Sporadic.Fischer.Fi22.TransvectionComparison
