module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 8

This bounded compilation unit checks labels 2048 through 2303.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check2048 : BitNetwork.check (edgeCheck true) 2048 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2080 : BitNetwork.check (edgeCheck true) 2080 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2112 : BitNetwork.check (edgeCheck true) 2112 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2144 : BitNetwork.check (edgeCheck true) 2144 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2176 : BitNetwork.check (edgeCheck true) 2176 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2208 : BitNetwork.check (edgeCheck true) 2208 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2240 : BitNetwork.check (edgeCheck true) 2240 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2272 : BitNetwork.check (edgeCheck true) 2272 32 = true := by
  decide +kernel

public theorem checkedB08 : BitNetwork.check (edgeCheck true) 2048 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 2048 32 224
    check2048 (BitNetwork.check_append (edgeCheck true) 2080 32 192
    check2080 (BitNetwork.check_append (edgeCheck true) 2112 32 160
    check2112 (BitNetwork.check_append (edgeCheck true) 2144 32 128
    check2144 (BitNetwork.check_append (edgeCheck true) 2176 32 96
    check2176 (BitNetwork.check_append (edgeCheck true) 2208 32 64
    check2208 (BitNetwork.check_append (edgeCheck true) 2240 32 32
    check2240 check2272)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
