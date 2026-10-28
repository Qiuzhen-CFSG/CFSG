module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Edges.Data

/-!
# Fi22 B edge certificate block 7

This bounded compilation unit checks labels 1792 through 2047.
Tree edges cancel algebraically; the other edges agree with certified subgroup
products on the faithful 48 coordinates. FamilyB joins the checked ranges.
Source: ATLAS F22G1-p3510B0 and the conjugation action after GLS3 Table 5.3t.
-/

namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

set_option maxRecDepth 4096 in
private theorem check1792 : BitNetwork.check (edgeCheck true) 1792 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1824 : BitNetwork.check (edgeCheck true) 1824 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1856 : BitNetwork.check (edgeCheck true) 1856 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1888 : BitNetwork.check (edgeCheck true) 1888 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1920 : BitNetwork.check (edgeCheck true) 1920 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1952 : BitNetwork.check (edgeCheck true) 1952 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check1984 : BitNetwork.check (edgeCheck true) 1984 32 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem check2016 : BitNetwork.check (edgeCheck true) 2016 32 = true := by
  decide +kernel

public theorem checkedB07 : BitNetwork.check (edgeCheck true) 1792 256 = true :=
  (BitNetwork.check_append (edgeCheck true) 1792 32 224
    check1792 (BitNetwork.check_append (edgeCheck true) 1824 32 192
    check1824 (BitNetwork.check_append (edgeCheck true) 1856 32 160
    check1856 (BitNetwork.check_append (edgeCheck true) 1888 32 128
    check1888 (BitNetwork.check_append (edgeCheck true) 1920 32 96
    check1920 (BitNetwork.check_append (edgeCheck true) 1952 32 64
    check1952 (BitNetwork.check_append (edgeCheck true) 1984 32 32
    check1984 check2016)))))))

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
