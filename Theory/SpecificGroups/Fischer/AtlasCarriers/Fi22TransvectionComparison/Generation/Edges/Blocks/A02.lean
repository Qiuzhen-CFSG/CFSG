module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 A edge certificate block 2

This bounded compilation unit checks labels 512 through 767.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyA joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check512 : BitNetwork.check (edgeCheck false) 512 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check544 : BitNetwork.check (edgeCheck false) 544 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check576 : BitNetwork.check (edgeCheck false) 576 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check608 : BitNetwork.check (edgeCheck false) 608 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check640 : BitNetwork.check (edgeCheck false) 640 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check672 : BitNetwork.check (edgeCheck false) 672 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check704 : BitNetwork.check (edgeCheck false) 704 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check736 : BitNetwork.check (edgeCheck false) 736 32 = true := by
  decide +kernel

public theorem checkedA02 : BitNetwork.check (edgeCheck false) 512 256 = true :=
  (BitNetwork.check_append (edgeCheck false) 512 32 224
    check512 (BitNetwork.check_append (edgeCheck false) 544 32 192
    check544 (BitNetwork.check_append (edgeCheck false) 576 32 160
    check576 (BitNetwork.check_append (edgeCheck false) 608 32 128
    check608 (BitNetwork.check_append (edgeCheck false) 640 32 96
    check640 (BitNetwork.check_append (edgeCheck false) 672 32 64
    check672 (BitNetwork.check_append (edgeCheck false) 704 32 32
    check704 check736)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
