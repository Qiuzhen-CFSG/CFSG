module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 10

This bounded compilation unit checks labels 2560 through 2815.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check2560 : BitNetwork.check (edgeCheck true) 2560 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2592 : BitNetwork.check (edgeCheck true) 2592 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2624 : BitNetwork.check (edgeCheck true) 2624 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2656 : BitNetwork.check (edgeCheck true) 2656 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2688 : BitNetwork.check (edgeCheck true) 2688 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2720 : BitNetwork.check (edgeCheck true) 2720 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2752 : BitNetwork.check (edgeCheck true) 2752 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2784 : BitNetwork.check (edgeCheck true) 2784 32 = true := by
  decide +kernel

public theorem checkedB10 : BitNetwork.check (edgeCheck true) 2560 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 2560 32 224
    check2560 (BitNetwork.check_append (edgeCheck true) 2592 32 192
    check2592 (BitNetwork.check_append (edgeCheck true) 2624 32 160
    check2624 (BitNetwork.check_append (edgeCheck true) 2656 32 128
    check2656 (BitNetwork.check_append (edgeCheck true) 2688 32 96
    check2688 (BitNetwork.check_append (edgeCheck true) 2720 32 64
    check2720 (BitNetwork.check_append (edgeCheck true) 2752 32 32
    check2752 check2784)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
