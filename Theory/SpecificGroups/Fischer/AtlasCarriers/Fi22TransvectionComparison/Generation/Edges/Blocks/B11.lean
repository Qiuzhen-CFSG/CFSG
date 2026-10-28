module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 11

This bounded compilation unit checks labels 2816 through 3071.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check2816 : BitNetwork.check (edgeCheck true) 2816 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2848 : BitNetwork.check (edgeCheck true) 2848 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2880 : BitNetwork.check (edgeCheck true) 2880 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2912 : BitNetwork.check (edgeCheck true) 2912 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2944 : BitNetwork.check (edgeCheck true) 2944 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2976 : BitNetwork.check (edgeCheck true) 2976 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3008 : BitNetwork.check (edgeCheck true) 3008 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3040 : BitNetwork.check (edgeCheck true) 3040 32 = true := by
  decide +kernel

public theorem checkedB11 : BitNetwork.check (edgeCheck true) 2816 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 2816 32 224
    check2816 (BitNetwork.check_append (edgeCheck true) 2848 32 192
    check2848 (BitNetwork.check_append (edgeCheck true) 2880 32 160
    check2880 (BitNetwork.check_append (edgeCheck true) 2912 32 128
    check2912 (BitNetwork.check_append (edgeCheck true) 2944 32 96
    check2944 (BitNetwork.check_append (edgeCheck true) 2976 32 64
    check2976 (BitNetwork.check_append (edgeCheck true) 3008 32 32
    check3008 check3040)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
