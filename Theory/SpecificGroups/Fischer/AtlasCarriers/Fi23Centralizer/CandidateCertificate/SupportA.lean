module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedGenerators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesA6

/-!
# Disjoint cycle support and lookup action for the Fi23 generator A

The block certificates combine by disjoint bit masks. The result certifies
both the support of the original decoded cycle product and the inverse action
on each of its cycles. Fixed complements are supplied by the point certificates.
Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
open KernelCertificate
set_option Elab.async false

private def tailMaskA61 : Nat := 0
private theorem tailSupportA61 : Supported ([] : List (List (List (Fin 31671)))).flatten.flatten tailMaskA61 := ⟨by simp, rfl⟩

private def tailMaskA60 : Nat := maskA60 ||| tailMaskA61
private theorem tailSupportA60 : Supported [cyclesA60].flatten.flatten tailMaskA60 := by
  exact Supported.blocks_cons (p := cyclesA60) (ps := [])
    supportA60 tailSupportA61 (by decide +kernel) rfl

private def tailMaskA59 : Nat := maskA59 ||| tailMaskA60
private theorem tailSupportA59 : Supported [cyclesA59, cyclesA60].flatten.flatten tailMaskA59 := by
  exact Supported.blocks_cons (p := cyclesA59) (ps := [cyclesA60])
    supportA59 tailSupportA60 (by decide +kernel) rfl

private def tailMaskA58 : Nat := maskA58 ||| tailMaskA59
private theorem tailSupportA58 : Supported [cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA58 := by
  exact Supported.blocks_cons (p := cyclesA58) (ps := [cyclesA59, cyclesA60])
    supportA58 tailSupportA59 (by decide +kernel) rfl

private def tailMaskA57 : Nat := maskA57 ||| tailMaskA58
private theorem tailSupportA57 : Supported [cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA57 := by
  exact Supported.blocks_cons (p := cyclesA57) (ps := [cyclesA58, cyclesA59, cyclesA60])
    supportA57 tailSupportA58 (by decide +kernel) rfl

private def tailMaskA56 : Nat := maskA56 ||| tailMaskA57
private theorem tailSupportA56 : Supported [cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA56 := by
  exact Supported.blocks_cons (p := cyclesA56) (ps := [cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA56 tailSupportA57 (by decide +kernel) rfl

private def tailMaskA55 : Nat := maskA55 ||| tailMaskA56
private theorem tailSupportA55 : Supported [cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA55 := by
  exact Supported.blocks_cons (p := cyclesA55) (ps := [cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA55 tailSupportA56 (by decide +kernel) rfl

private def tailMaskA54 : Nat := maskA54 ||| tailMaskA55
private theorem tailSupportA54 : Supported [cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA54 := by
  exact Supported.blocks_cons (p := cyclesA54) (ps := [cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA54 tailSupportA55 (by decide +kernel) rfl

private def tailMaskA53 : Nat := maskA53 ||| tailMaskA54
private theorem tailSupportA53 : Supported [cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA53 := by
  exact Supported.blocks_cons (p := cyclesA53) (ps := [cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA53 tailSupportA54 (by decide +kernel) rfl

private def tailMaskA52 : Nat := maskA52 ||| tailMaskA53
private theorem tailSupportA52 : Supported [cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA52 := by
  exact Supported.blocks_cons (p := cyclesA52) (ps := [cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA52 tailSupportA53 (by decide +kernel) rfl

private def tailMaskA51 : Nat := maskA51 ||| tailMaskA52
private theorem tailSupportA51 : Supported [cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA51 := by
  exact Supported.blocks_cons (p := cyclesA51) (ps := [cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA51 tailSupportA52 (by decide +kernel) rfl

private def tailMaskA50 : Nat := maskA50 ||| tailMaskA51
private theorem tailSupportA50 : Supported [cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA50 := by
  exact Supported.blocks_cons (p := cyclesA50) (ps := [cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA50 tailSupportA51 (by decide +kernel) rfl

private def tailMaskA49 : Nat := maskA49 ||| tailMaskA50
private theorem tailSupportA49 : Supported [cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA49 := by
  exact Supported.blocks_cons (p := cyclesA49) (ps := [cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA49 tailSupportA50 (by decide +kernel) rfl

private def tailMaskA48 : Nat := maskA48 ||| tailMaskA49
private theorem tailSupportA48 : Supported [cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA48 := by
  exact Supported.blocks_cons (p := cyclesA48) (ps := [cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA48 tailSupportA49 (by decide +kernel) rfl

private def tailMaskA47 : Nat := maskA47 ||| tailMaskA48
private theorem tailSupportA47 : Supported [cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA47 := by
  exact Supported.blocks_cons (p := cyclesA47) (ps := [cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA47 tailSupportA48 (by decide +kernel) rfl

private def tailMaskA46 : Nat := maskA46 ||| tailMaskA47
private theorem tailSupportA46 : Supported [cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA46 := by
  exact Supported.blocks_cons (p := cyclesA46) (ps := [cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA46 tailSupportA47 (by decide +kernel) rfl

private def tailMaskA45 : Nat := maskA45 ||| tailMaskA46
private theorem tailSupportA45 : Supported [cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA45 := by
  exact Supported.blocks_cons (p := cyclesA45) (ps := [cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA45 tailSupportA46 (by decide +kernel) rfl

private def tailMaskA44 : Nat := maskA44 ||| tailMaskA45
private theorem tailSupportA44 : Supported [cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA44 := by
  exact Supported.blocks_cons (p := cyclesA44) (ps := [cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA44 tailSupportA45 (by decide +kernel) rfl

private def tailMaskA43 : Nat := maskA43 ||| tailMaskA44
private theorem tailSupportA43 : Supported [cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA43 := by
  exact Supported.blocks_cons (p := cyclesA43) (ps := [cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA43 tailSupportA44 (by decide +kernel) rfl

private def tailMaskA42 : Nat := maskA42 ||| tailMaskA43
private theorem tailSupportA42 : Supported [cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA42 := by
  exact Supported.blocks_cons (p := cyclesA42) (ps := [cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA42 tailSupportA43 (by decide +kernel) rfl

private def tailMaskA41 : Nat := maskA41 ||| tailMaskA42
private theorem tailSupportA41 : Supported [cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA41 := by
  exact Supported.blocks_cons (p := cyclesA41) (ps := [cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA41 tailSupportA42 (by decide +kernel) rfl

private def tailMaskA40 : Nat := maskA40 ||| tailMaskA41
private theorem tailSupportA40 : Supported [cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA40 := by
  exact Supported.blocks_cons (p := cyclesA40) (ps := [cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA40 tailSupportA41 (by decide +kernel) rfl

private def tailMaskA39 : Nat := maskA39 ||| tailMaskA40
private theorem tailSupportA39 : Supported [cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA39 := by
  exact Supported.blocks_cons (p := cyclesA39) (ps := [cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA39 tailSupportA40 (by decide +kernel) rfl

private def tailMaskA38 : Nat := maskA38 ||| tailMaskA39
private theorem tailSupportA38 : Supported [cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA38 := by
  exact Supported.blocks_cons (p := cyclesA38) (ps := [cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA38 tailSupportA39 (by decide +kernel) rfl

private def tailMaskA37 : Nat := maskA37 ||| tailMaskA38
private theorem tailSupportA37 : Supported [cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA37 := by
  exact Supported.blocks_cons (p := cyclesA37) (ps := [cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA37 tailSupportA38 (by decide +kernel) rfl

private def tailMaskA36 : Nat := maskA36 ||| tailMaskA37
private theorem tailSupportA36 : Supported [cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA36 := by
  exact Supported.blocks_cons (p := cyclesA36) (ps := [cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA36 tailSupportA37 (by decide +kernel) rfl

private def tailMaskA35 : Nat := maskA35 ||| tailMaskA36
private theorem tailSupportA35 : Supported [cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA35 := by
  exact Supported.blocks_cons (p := cyclesA35) (ps := [cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA35 tailSupportA36 (by decide +kernel) rfl

private def tailMaskA34 : Nat := maskA34 ||| tailMaskA35
private theorem tailSupportA34 : Supported [cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA34 := by
  exact Supported.blocks_cons (p := cyclesA34) (ps := [cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA34 tailSupportA35 (by decide +kernel) rfl

private def tailMaskA33 : Nat := maskA33 ||| tailMaskA34
private theorem tailSupportA33 : Supported [cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA33 := by
  exact Supported.blocks_cons (p := cyclesA33) (ps := [cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA33 tailSupportA34 (by decide +kernel) rfl

private def tailMaskA32 : Nat := maskA32 ||| tailMaskA33
private theorem tailSupportA32 : Supported [cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA32 := by
  exact Supported.blocks_cons (p := cyclesA32) (ps := [cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA32 tailSupportA33 (by decide +kernel) rfl

private def tailMaskA31 : Nat := maskA31 ||| tailMaskA32
private theorem tailSupportA31 : Supported [cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA31 := by
  exact Supported.blocks_cons (p := cyclesA31) (ps := [cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA31 tailSupportA32 (by decide +kernel) rfl

private def tailMaskA30 : Nat := maskA30 ||| tailMaskA31
private theorem tailSupportA30 : Supported [cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA30 := by
  exact Supported.blocks_cons (p := cyclesA30) (ps := [cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA30 tailSupportA31 (by decide +kernel) rfl

private def tailMaskA29 : Nat := maskA29 ||| tailMaskA30
private theorem tailSupportA29 : Supported [cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA29 := by
  exact Supported.blocks_cons (p := cyclesA29) (ps := [cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA29 tailSupportA30 (by decide +kernel) rfl

private def tailMaskA28 : Nat := maskA28 ||| tailMaskA29
private theorem tailSupportA28 : Supported [cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA28 := by
  exact Supported.blocks_cons (p := cyclesA28) (ps := [cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA28 tailSupportA29 (by decide +kernel) rfl

private def tailMaskA27 : Nat := maskA27 ||| tailMaskA28
private theorem tailSupportA27 : Supported [cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA27 := by
  exact Supported.blocks_cons (p := cyclesA27) (ps := [cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA27 tailSupportA28 (by decide +kernel) rfl

private def tailMaskA26 : Nat := maskA26 ||| tailMaskA27
private theorem tailSupportA26 : Supported [cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA26 := by
  exact Supported.blocks_cons (p := cyclesA26) (ps := [cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA26 tailSupportA27 (by decide +kernel) rfl

private def tailMaskA25 : Nat := maskA25 ||| tailMaskA26
private theorem tailSupportA25 : Supported [cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA25 := by
  exact Supported.blocks_cons (p := cyclesA25) (ps := [cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA25 tailSupportA26 (by decide +kernel) rfl

private def tailMaskA24 : Nat := maskA24 ||| tailMaskA25
private theorem tailSupportA24 : Supported [cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA24 := by
  exact Supported.blocks_cons (p := cyclesA24) (ps := [cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA24 tailSupportA25 (by decide +kernel) rfl

private def tailMaskA23 : Nat := maskA23 ||| tailMaskA24
private theorem tailSupportA23 : Supported [cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA23 := by
  exact Supported.blocks_cons (p := cyclesA23) (ps := [cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA23 tailSupportA24 (by decide +kernel) rfl

private def tailMaskA22 : Nat := maskA22 ||| tailMaskA23
private theorem tailSupportA22 : Supported [cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA22 := by
  exact Supported.blocks_cons (p := cyclesA22) (ps := [cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA22 tailSupportA23 (by decide +kernel) rfl

private def tailMaskA21 : Nat := maskA21 ||| tailMaskA22
private theorem tailSupportA21 : Supported [cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA21 := by
  exact Supported.blocks_cons (p := cyclesA21) (ps := [cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA21 tailSupportA22 (by decide +kernel) rfl

private def tailMaskA20 : Nat := maskA20 ||| tailMaskA21
private theorem tailSupportA20 : Supported [cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA20 := by
  exact Supported.blocks_cons (p := cyclesA20) (ps := [cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA20 tailSupportA21 (by decide +kernel) rfl

private def tailMaskA19 : Nat := maskA19 ||| tailMaskA20
private theorem tailSupportA19 : Supported [cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA19 := by
  exact Supported.blocks_cons (p := cyclesA19) (ps := [cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA19 tailSupportA20 (by decide +kernel) rfl

private def tailMaskA18 : Nat := maskA18 ||| tailMaskA19
private theorem tailSupportA18 : Supported [cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA18 := by
  exact Supported.blocks_cons (p := cyclesA18) (ps := [cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA18 tailSupportA19 (by decide +kernel) rfl

private def tailMaskA17 : Nat := maskA17 ||| tailMaskA18
private theorem tailSupportA17 : Supported [cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA17 := by
  exact Supported.blocks_cons (p := cyclesA17) (ps := [cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA17 tailSupportA18 (by decide +kernel) rfl

private def tailMaskA16 : Nat := maskA16 ||| tailMaskA17
private theorem tailSupportA16 : Supported [cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA16 := by
  exact Supported.blocks_cons (p := cyclesA16) (ps := [cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA16 tailSupportA17 (by decide +kernel) rfl

private def tailMaskA15 : Nat := maskA15 ||| tailMaskA16
private theorem tailSupportA15 : Supported [cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA15 := by
  exact Supported.blocks_cons (p := cyclesA15) (ps := [cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA15 tailSupportA16 (by decide +kernel) rfl

private def tailMaskA14 : Nat := maskA14 ||| tailMaskA15
private theorem tailSupportA14 : Supported [cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA14 := by
  exact Supported.blocks_cons (p := cyclesA14) (ps := [cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA14 tailSupportA15 (by decide +kernel) rfl

private def tailMaskA13 : Nat := maskA13 ||| tailMaskA14
private theorem tailSupportA13 : Supported [cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA13 := by
  exact Supported.blocks_cons (p := cyclesA13) (ps := [cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA13 tailSupportA14 (by decide +kernel) rfl

private def tailMaskA12 : Nat := maskA12 ||| tailMaskA13
private theorem tailSupportA12 : Supported [cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA12 := by
  exact Supported.blocks_cons (p := cyclesA12) (ps := [cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA12 tailSupportA13 (by decide +kernel) rfl

private def tailMaskA11 : Nat := maskA11 ||| tailMaskA12
private theorem tailSupportA11 : Supported [cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA11 := by
  exact Supported.blocks_cons (p := cyclesA11) (ps := [cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA11 tailSupportA12 (by decide +kernel) rfl

private def tailMaskA10 : Nat := maskA10 ||| tailMaskA11
private theorem tailSupportA10 : Supported [cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA10 := by
  exact Supported.blocks_cons (p := cyclesA10) (ps := [cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA10 tailSupportA11 (by decide +kernel) rfl

private def tailMaskA9 : Nat := maskA9 ||| tailMaskA10
private theorem tailSupportA9 : Supported [cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA9 := by
  exact Supported.blocks_cons (p := cyclesA9) (ps := [cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA9 tailSupportA10 (by decide +kernel) rfl

private def tailMaskA8 : Nat := maskA8 ||| tailMaskA9
private theorem tailSupportA8 : Supported [cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA8 := by
  exact Supported.blocks_cons (p := cyclesA8) (ps := [cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA8 tailSupportA9 (by decide +kernel) rfl

private def tailMaskA7 : Nat := maskA7 ||| tailMaskA8
private theorem tailSupportA7 : Supported [cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA7 := by
  exact Supported.blocks_cons (p := cyclesA7) (ps := [cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA7 tailSupportA8 (by decide +kernel) rfl

private def tailMaskA6 : Nat := maskA6 ||| tailMaskA7
private theorem tailSupportA6 : Supported [cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA6 := by
  exact Supported.blocks_cons (p := cyclesA6) (ps := [cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA6 tailSupportA7 (by decide +kernel) rfl

private def tailMaskA5 : Nat := maskA5 ||| tailMaskA6
private theorem tailSupportA5 : Supported [cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA5 := by
  exact Supported.blocks_cons (p := cyclesA5) (ps := [cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA5 tailSupportA6 (by decide +kernel) rfl

private def tailMaskA4 : Nat := maskA4 ||| tailMaskA5
private theorem tailSupportA4 : Supported [cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA4 := by
  exact Supported.blocks_cons (p := cyclesA4) (ps := [cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA4 tailSupportA5 (by decide +kernel) rfl

private def tailMaskA3 : Nat := maskA3 ||| tailMaskA4
private theorem tailSupportA3 : Supported [cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA3 := by
  exact Supported.blocks_cons (p := cyclesA3) (ps := [cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA3 tailSupportA4 (by decide +kernel) rfl

private def tailMaskA2 : Nat := maskA2 ||| tailMaskA3
private theorem tailSupportA2 : Supported [cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA2 := by
  exact Supported.blocks_cons (p := cyclesA2) (ps := [cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA2 tailSupportA3 (by decide +kernel) rfl

private def tailMaskA1 : Nat := maskA1 ||| tailMaskA2
private theorem tailSupportA1 : Supported [cyclesA1, cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA1 := by
  exact Supported.blocks_cons (p := cyclesA1) (ps := [cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA1 tailSupportA2 (by decide +kernel) rfl

private def tailMaskA0 : Nat := maskA0 ||| tailMaskA1
private theorem tailSupportA0 : Supported [cyclesA0, cyclesA1, cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60].flatten.flatten tailMaskA0 := by
  exact Supported.blocks_cons (p := cyclesA0) (ps := [cyclesA1, cyclesA2, cyclesA3, cyclesA4, cyclesA5, cyclesA6, cyclesA7, cyclesA8, cyclesA9, cyclesA10, cyclesA11, cyclesA12, cyclesA13, cyclesA14, cyclesA15, cyclesA16, cyclesA17, cyclesA18, cyclesA19, cyclesA20, cyclesA21, cyclesA22, cyclesA23, cyclesA24, cyclesA25, cyclesA26, cyclesA27, cyclesA28, cyclesA29, cyclesA30, cyclesA31, cyclesA32, cyclesA33, cyclesA34, cyclesA35, cyclesA36, cyclesA37, cyclesA38, cyclesA39, cyclesA40, cyclesA41, cyclesA42, cyclesA43, cyclesA44, cyclesA45, cyclesA46, cyclesA47, cyclesA48, cyclesA49, cyclesA50, cyclesA51, cyclesA52, cyclesA53, cyclesA54, cyclesA55, cyclesA56, cyclesA57, cyclesA58, cyclesA59, cyclesA60])
    supportA0 tailSupportA1 (by decide +kernel) rfl

theorem supportA : Supported cyclesA.flatten supportMaskA := by
  have hm : tailMaskA0 = supportMaskA := by decide +kernel
  exact hm ▸ tailSupportA0

theorem actionA :
    (cyclesA.all fun c => c.all fun x => decide (c.formPerm (aMap x) = x)) = true := by
  simp only [cyclesA, List.all_flatten, List.all_cons, List.all_nil,
    actionA0, actionA1, actionA2, actionA3, actionA4, actionA5, actionA6, actionA7, actionA8, actionA9, actionA10, actionA11, actionA12, actionA13, actionA14, actionA15, actionA16, actionA17, actionA18, actionA19, actionA20, actionA21, actionA22, actionA23, actionA24, actionA25, actionA26, actionA27, actionA28, actionA29, actionA30, actionA31, actionA32, actionA33, actionA34, actionA35, actionA36, actionA37, actionA38, actionA39, actionA40, actionA41, actionA42, actionA43, actionA44, actionA45, actionA46, actionA47, actionA48, actionA49, actionA50, actionA51, actionA52, actionA53, actionA54, actionA55, actionA56, actionA57, actionA58, actionA59, actionA60, Bool.true_and]

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
