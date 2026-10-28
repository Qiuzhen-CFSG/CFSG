module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 1

This bounded compilation unit checks labels 256 through 511.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check256 : BitNetwork.check (edgeCheck true) 256 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check288 : BitNetwork.check (edgeCheck true) 288 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check320 : BitNetwork.check (edgeCheck true) 320 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check352 : BitNetwork.check (edgeCheck true) 352 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check384 : BitNetwork.check (edgeCheck true) 384 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check416 : BitNetwork.check (edgeCheck true) 416 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check448 : BitNetwork.check (edgeCheck true) 448 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check480 : BitNetwork.check (edgeCheck true) 480 32 = true := by
  decide +kernel

public theorem checkedB01 : BitNetwork.check (edgeCheck true) 256 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 256 32 224
    check256 (BitNetwork.check_append (edgeCheck true) 288 32 192
    check288 (BitNetwork.check_append (edgeCheck true) 320 32 160
    check320 (BitNetwork.check_append (edgeCheck true) 352 32 128
    check352 (BitNetwork.check_append (edgeCheck true) 384 32 96
    check384 (BitNetwork.check_append (edgeCheck true) 416 32 64
    check416 (BitNetwork.check_append (edgeCheck true) 448 32 32
    check448 check480)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
