module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 12

This bounded compilation unit checks labels 3072 through 3327.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check3072 : BitNetwork.check (edgeCheck true) 3072 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3104 : BitNetwork.check (edgeCheck true) 3104 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3136 : BitNetwork.check (edgeCheck true) 3136 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3168 : BitNetwork.check (edgeCheck true) 3168 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3200 : BitNetwork.check (edgeCheck true) 3200 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3232 : BitNetwork.check (edgeCheck true) 3232 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3264 : BitNetwork.check (edgeCheck true) 3264 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3296 : BitNetwork.check (edgeCheck true) 3296 32 = true := by
  decide +kernel

public theorem checkedB12 : BitNetwork.check (edgeCheck true) 3072 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 3072 32 224
    check3072 (BitNetwork.check_append (edgeCheck true) 3104 32 192
    check3104 (BitNetwork.check_append (edgeCheck true) 3136 32 160
    check3136 (BitNetwork.check_append (edgeCheck true) 3168 32 128
    check3168 (BitNetwork.check_append (edgeCheck true) 3200 32 96
    check3200 (BitNetwork.check_append (edgeCheck true) 3232 32 64
    check3232 (BitNetwork.check_append (edgeCheck true) 3264 32 32
    check3264 check3296)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
