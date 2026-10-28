module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 3

This bounded compilation unit checks labels 768 through 1023.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check768 : BitNetwork.check (edgeCheck true) 768 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check800 : BitNetwork.check (edgeCheck true) 800 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check832 : BitNetwork.check (edgeCheck true) 832 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check864 : BitNetwork.check (edgeCheck true) 864 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check896 : BitNetwork.check (edgeCheck true) 896 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check928 : BitNetwork.check (edgeCheck true) 928 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check960 : BitNetwork.check (edgeCheck true) 960 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check992 : BitNetwork.check (edgeCheck true) 992 32 = true := by
  decide +kernel

public theorem checkedB03 : BitNetwork.check (edgeCheck true) 768 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 768 32 224
    check768 (BitNetwork.check_append (edgeCheck true) 800 32 192
    check800 (BitNetwork.check_append (edgeCheck true) 832 32 160
    check832 (BitNetwork.check_append (edgeCheck true) 864 32 128
    check864 (BitNetwork.check_append (edgeCheck true) 896 32 96
    check896 (BitNetwork.check_append (edgeCheck true) 928 32 64
    check928 (BitNetwork.check_append (edgeCheck true) 960 32 32
    check960 check992)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
