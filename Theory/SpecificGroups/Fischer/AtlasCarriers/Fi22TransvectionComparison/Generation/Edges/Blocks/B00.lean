module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 0

This bounded compilation unit checks labels 0 through 255.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check0 : BitNetwork.check (edgeCheck true) 0 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check32 : BitNetwork.check (edgeCheck true) 32 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check64 : BitNetwork.check (edgeCheck true) 64 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check96 : BitNetwork.check (edgeCheck true) 96 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check128 : BitNetwork.check (edgeCheck true) 128 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check160 : BitNetwork.check (edgeCheck true) 160 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check192 : BitNetwork.check (edgeCheck true) 192 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check224 : BitNetwork.check (edgeCheck true) 224 32 = true := by
  decide +kernel

public theorem checkedB00 : BitNetwork.check (edgeCheck true) 0 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 0 32 224
    check0 (BitNetwork.check_append (edgeCheck true) 32 32 192
    check32 (BitNetwork.check_append (edgeCheck true) 64 32 160
    check64 (BitNetwork.check_append (edgeCheck true) 96 32 128
    check96 (BitNetwork.check_append (edgeCheck true) 128 32 96
    check128 (BitNetwork.check_append (edgeCheck true) 160 32 64
    check160 (BitNetwork.check_append (edgeCheck true) 192 32 32
    check192 check224)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
