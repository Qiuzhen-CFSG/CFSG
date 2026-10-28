module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 6

This bounded compilation unit checks labels 1536 through 1791.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check1536 : BitNetwork.check (edgeCheck true) 1536 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1568 : BitNetwork.check (edgeCheck true) 1568 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1600 : BitNetwork.check (edgeCheck true) 1600 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1632 : BitNetwork.check (edgeCheck true) 1632 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1664 : BitNetwork.check (edgeCheck true) 1664 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1696 : BitNetwork.check (edgeCheck true) 1696 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1728 : BitNetwork.check (edgeCheck true) 1728 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1760 : BitNetwork.check (edgeCheck true) 1760 32 = true := by
  decide +kernel

public theorem checkedB06 : BitNetwork.check (edgeCheck true) 1536 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 1536 32 224
    check1536 (BitNetwork.check_append (edgeCheck true) 1568 32 192
    check1568 (BitNetwork.check_append (edgeCheck true) 1600 32 160
    check1600 (BitNetwork.check_append (edgeCheck true) 1632 32 128
    check1632 (BitNetwork.check_append (edgeCheck true) 1664 32 96
    check1664 (BitNetwork.check_append (edgeCheck true) 1696 32 64
    check1696 (BitNetwork.check_append (edgeCheck true) 1728 32 32
    check1728 check1760)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
