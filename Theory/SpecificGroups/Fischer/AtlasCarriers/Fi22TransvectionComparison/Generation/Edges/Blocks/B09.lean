module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 9

This bounded compilation unit checks labels 2304 through 2559.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check2304 : BitNetwork.check (edgeCheck true) 2304 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2336 : BitNetwork.check (edgeCheck true) 2336 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2368 : BitNetwork.check (edgeCheck true) 2368 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2400 : BitNetwork.check (edgeCheck true) 2400 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2432 : BitNetwork.check (edgeCheck true) 2432 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2464 : BitNetwork.check (edgeCheck true) 2464 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2496 : BitNetwork.check (edgeCheck true) 2496 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2528 : BitNetwork.check (edgeCheck true) 2528 32 = true := by
  decide +kernel

public theorem checkedB09 : BitNetwork.check (edgeCheck true) 2304 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 2304 32 224
    check2304 (BitNetwork.check_append (edgeCheck true) 2336 32 192
    check2336 (BitNetwork.check_append (edgeCheck true) 2368 32 160
    check2368 (BitNetwork.check_append (edgeCheck true) 2400 32 128
    check2400 (BitNetwork.check_append (edgeCheck true) 2432 32 96
    check2432 (BitNetwork.check_append (edgeCheck true) 2464 32 64
    check2464 (BitNetwork.check_append (edgeCheck true) 2496 32 32
    check2496 check2528)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
