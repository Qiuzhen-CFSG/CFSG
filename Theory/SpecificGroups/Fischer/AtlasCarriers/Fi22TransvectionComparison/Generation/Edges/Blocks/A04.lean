module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 A edge certificate block 4

This bounded compilation unit checks labels 1024 through 1279.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyA joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check1024 : BitNetwork.check (edgeCheck false) 1024 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1056 : BitNetwork.check (edgeCheck false) 1056 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1088 : BitNetwork.check (edgeCheck false) 1088 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1120 : BitNetwork.check (edgeCheck false) 1120 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1152 : BitNetwork.check (edgeCheck false) 1152 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1184 : BitNetwork.check (edgeCheck false) 1184 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1216 : BitNetwork.check (edgeCheck false) 1216 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1248 : BitNetwork.check (edgeCheck false) 1248 32 = true := by
  decide +kernel

public theorem checkedA04 : BitNetwork.check (edgeCheck false) 1024 256 = true :=
  (BitNetwork.check_append (edgeCheck false) 1024 32 224
    check1024 (BitNetwork.check_append (edgeCheck false) 1056 32 192
    check1056 (BitNetwork.check_append (edgeCheck false) 1088 32 160
    check1088 (BitNetwork.check_append (edgeCheck false) 1120 32 128
    check1120 (BitNetwork.check_append (edgeCheck false) 1152 32 96
    check1152 (BitNetwork.check_append (edgeCheck false) 1184 32 64
    check1184 (BitNetwork.check_append (edgeCheck false) 1216 32 32
    check1216 check1248)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
