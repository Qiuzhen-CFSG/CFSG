module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 A edge certificate block 5

This bounded compilation unit checks labels 1280 through 1535.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyA joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check1280 : BitNetwork.check (edgeCheck false) 1280 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1312 : BitNetwork.check (edgeCheck false) 1312 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1344 : BitNetwork.check (edgeCheck false) 1344 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1376 : BitNetwork.check (edgeCheck false) 1376 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1408 : BitNetwork.check (edgeCheck false) 1408 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1440 : BitNetwork.check (edgeCheck false) 1440 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1472 : BitNetwork.check (edgeCheck false) 1472 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1504 : BitNetwork.check (edgeCheck false) 1504 32 = true := by
  decide +kernel

public theorem checkedA05 : BitNetwork.check (edgeCheck false) 1280 256 = true :=
  (BitNetwork.check_append (edgeCheck false) 1280 32 224
    check1280 (BitNetwork.check_append (edgeCheck false) 1312 32 192
    check1312 (BitNetwork.check_append (edgeCheck false) 1344 32 160
    check1344 (BitNetwork.check_append (edgeCheck false) 1376 32 128
    check1376 (BitNetwork.check_append (edgeCheck false) 1408 32 96
    check1408 (BitNetwork.check_append (edgeCheck false) 1440 32 64
    check1440 (BitNetwork.check_append (edgeCheck false) 1472 32 32
    check1472 check1504)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
