module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 A edge certificate block 13

This bounded compilation unit checks labels 3328 through 3509.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyA joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check3328 : BitNetwork.check (edgeCheck false) 3328 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3360 : BitNetwork.check (edgeCheck false) 3360 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3392 : BitNetwork.check (edgeCheck false) 3392 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3424 : BitNetwork.check (edgeCheck false) 3424 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3456 : BitNetwork.check (edgeCheck false) 3456 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check3488 : BitNetwork.check (edgeCheck false) 3488 22 = true := by
  decide +kernel

public theorem checkedA13 : BitNetwork.check (edgeCheck false) 3328 182 = true :=
  (BitNetwork.check_append (edgeCheck false) 3328 32 150
    check3328 (BitNetwork.check_append (edgeCheck false) 3360 32 118
    check3360 (BitNetwork.check_append (edgeCheck false) 3392 32 86
    check3392 (BitNetwork.check_append (edgeCheck false) 3424 32 54
    check3424 (BitNetwork.check_append (edgeCheck false) 3456 32 22
    check3456 check3488)))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
