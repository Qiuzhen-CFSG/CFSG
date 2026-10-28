module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.DecodedGenerators
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.Predicates
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesB0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesB1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesB2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesB3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.CandidateCertificate.CyclesB4

/-!
# Disjoint cycle support and lookup action for the Fi23 generator B

The block certificates combine by disjoint bit masks. The result certifies
both the support of the original decoded cycle product and the inverse action
on each of its cycles. Fixed complements are supplied by the point certificates.
Source: ATLAS F23G1-p31671B0; application: GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
open KernelCertificate
set_option Elab.async false

private def tailMaskB42 : Nat := 0
private theorem tailSupportB42 : Supported ([] : List (List (List (Fin 31671)))).flatten.flatten tailMaskB42 := ⟨by simp, rfl⟩

private def tailMaskB41 : Nat := maskB41 ||| tailMaskB42
private theorem tailSupportB41 : Supported [cyclesB41].flatten.flatten tailMaskB41 := by
  exact Supported.blocks_cons (p := cyclesB41) (ps := [])
    supportB41 tailSupportB42 (by decide +kernel) rfl

private def tailMaskB40 : Nat := maskB40 ||| tailMaskB41
private theorem tailSupportB40 : Supported [cyclesB40, cyclesB41].flatten.flatten tailMaskB40 := by
  exact Supported.blocks_cons (p := cyclesB40) (ps := [cyclesB41])
    supportB40 tailSupportB41 (by decide +kernel) rfl

private def tailMaskB39 : Nat := maskB39 ||| tailMaskB40
private theorem tailSupportB39 : Supported [cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB39 := by
  exact Supported.blocks_cons (p := cyclesB39) (ps := [cyclesB40, cyclesB41])
    supportB39 tailSupportB40 (by decide +kernel) rfl

private def tailMaskB38 : Nat := maskB38 ||| tailMaskB39
private theorem tailSupportB38 : Supported [cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB38 := by
  exact Supported.blocks_cons (p := cyclesB38) (ps := [cyclesB39, cyclesB40, cyclesB41])
    supportB38 tailSupportB39 (by decide +kernel) rfl

private def tailMaskB37 : Nat := maskB37 ||| tailMaskB38
private theorem tailSupportB37 : Supported [cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB37 := by
  exact Supported.blocks_cons (p := cyclesB37) (ps := [cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB37 tailSupportB38 (by decide +kernel) rfl

private def tailMaskB36 : Nat := maskB36 ||| tailMaskB37
private theorem tailSupportB36 : Supported [cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB36 := by
  exact Supported.blocks_cons (p := cyclesB36) (ps := [cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB36 tailSupportB37 (by decide +kernel) rfl

private def tailMaskB35 : Nat := maskB35 ||| tailMaskB36
private theorem tailSupportB35 : Supported [cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB35 := by
  exact Supported.blocks_cons (p := cyclesB35) (ps := [cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB35 tailSupportB36 (by decide +kernel) rfl

private def tailMaskB34 : Nat := maskB34 ||| tailMaskB35
private theorem tailSupportB34 : Supported [cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB34 := by
  exact Supported.blocks_cons (p := cyclesB34) (ps := [cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB34 tailSupportB35 (by decide +kernel) rfl

private def tailMaskB33 : Nat := maskB33 ||| tailMaskB34
private theorem tailSupportB33 : Supported [cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB33 := by
  exact Supported.blocks_cons (p := cyclesB33) (ps := [cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB33 tailSupportB34 (by decide +kernel) rfl

private def tailMaskB32 : Nat := maskB32 ||| tailMaskB33
private theorem tailSupportB32 : Supported [cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB32 := by
  exact Supported.blocks_cons (p := cyclesB32) (ps := [cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB32 tailSupportB33 (by decide +kernel) rfl

private def tailMaskB31 : Nat := maskB31 ||| tailMaskB32
private theorem tailSupportB31 : Supported [cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB31 := by
  exact Supported.blocks_cons (p := cyclesB31) (ps := [cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB31 tailSupportB32 (by decide +kernel) rfl

private def tailMaskB30 : Nat := maskB30 ||| tailMaskB31
private theorem tailSupportB30 : Supported [cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB30 := by
  exact Supported.blocks_cons (p := cyclesB30) (ps := [cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB30 tailSupportB31 (by decide +kernel) rfl

private def tailMaskB29 : Nat := maskB29 ||| tailMaskB30
private theorem tailSupportB29 : Supported [cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB29 := by
  exact Supported.blocks_cons (p := cyclesB29) (ps := [cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB29 tailSupportB30 (by decide +kernel) rfl

private def tailMaskB28 : Nat := maskB28 ||| tailMaskB29
private theorem tailSupportB28 : Supported [cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB28 := by
  exact Supported.blocks_cons (p := cyclesB28) (ps := [cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB28 tailSupportB29 (by decide +kernel) rfl

private def tailMaskB27 : Nat := maskB27 ||| tailMaskB28
private theorem tailSupportB27 : Supported [cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB27 := by
  exact Supported.blocks_cons (p := cyclesB27) (ps := [cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB27 tailSupportB28 (by decide +kernel) rfl

private def tailMaskB26 : Nat := maskB26 ||| tailMaskB27
private theorem tailSupportB26 : Supported [cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB26 := by
  exact Supported.blocks_cons (p := cyclesB26) (ps := [cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB26 tailSupportB27 (by decide +kernel) rfl

private def tailMaskB25 : Nat := maskB25 ||| tailMaskB26
private theorem tailSupportB25 : Supported [cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB25 := by
  exact Supported.blocks_cons (p := cyclesB25) (ps := [cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB25 tailSupportB26 (by decide +kernel) rfl

private def tailMaskB24 : Nat := maskB24 ||| tailMaskB25
private theorem tailSupportB24 : Supported [cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB24 := by
  exact Supported.blocks_cons (p := cyclesB24) (ps := [cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB24 tailSupportB25 (by decide +kernel) rfl

private def tailMaskB23 : Nat := maskB23 ||| tailMaskB24
private theorem tailSupportB23 : Supported [cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB23 := by
  exact Supported.blocks_cons (p := cyclesB23) (ps := [cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB23 tailSupportB24 (by decide +kernel) rfl

private def tailMaskB22 : Nat := maskB22 ||| tailMaskB23
private theorem tailSupportB22 : Supported [cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB22 := by
  exact Supported.blocks_cons (p := cyclesB22) (ps := [cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB22 tailSupportB23 (by decide +kernel) rfl

private def tailMaskB21 : Nat := maskB21 ||| tailMaskB22
private theorem tailSupportB21 : Supported [cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB21 := by
  exact Supported.blocks_cons (p := cyclesB21) (ps := [cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB21 tailSupportB22 (by decide +kernel) rfl

private def tailMaskB20 : Nat := maskB20 ||| tailMaskB21
private theorem tailSupportB20 : Supported [cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB20 := by
  exact Supported.blocks_cons (p := cyclesB20) (ps := [cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB20 tailSupportB21 (by decide +kernel) rfl

private def tailMaskB19 : Nat := maskB19 ||| tailMaskB20
private theorem tailSupportB19 : Supported [cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB19 := by
  exact Supported.blocks_cons (p := cyclesB19) (ps := [cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB19 tailSupportB20 (by decide +kernel) rfl

private def tailMaskB18 : Nat := maskB18 ||| tailMaskB19
private theorem tailSupportB18 : Supported [cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB18 := by
  exact Supported.blocks_cons (p := cyclesB18) (ps := [cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB18 tailSupportB19 (by decide +kernel) rfl

private def tailMaskB17 : Nat := maskB17 ||| tailMaskB18
private theorem tailSupportB17 : Supported [cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB17 := by
  exact Supported.blocks_cons (p := cyclesB17) (ps := [cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB17 tailSupportB18 (by decide +kernel) rfl

private def tailMaskB16 : Nat := maskB16 ||| tailMaskB17
private theorem tailSupportB16 : Supported [cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB16 := by
  exact Supported.blocks_cons (p := cyclesB16) (ps := [cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB16 tailSupportB17 (by decide +kernel) rfl

private def tailMaskB15 : Nat := maskB15 ||| tailMaskB16
private theorem tailSupportB15 : Supported [cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB15 := by
  exact Supported.blocks_cons (p := cyclesB15) (ps := [cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB15 tailSupportB16 (by decide +kernel) rfl

private def tailMaskB14 : Nat := maskB14 ||| tailMaskB15
private theorem tailSupportB14 : Supported [cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB14 := by
  exact Supported.blocks_cons (p := cyclesB14) (ps := [cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB14 tailSupportB15 (by decide +kernel) rfl

private def tailMaskB13 : Nat := maskB13 ||| tailMaskB14
private theorem tailSupportB13 : Supported [cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB13 := by
  exact Supported.blocks_cons (p := cyclesB13) (ps := [cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB13 tailSupportB14 (by decide +kernel) rfl

private def tailMaskB12 : Nat := maskB12 ||| tailMaskB13
private theorem tailSupportB12 : Supported [cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB12 := by
  exact Supported.blocks_cons (p := cyclesB12) (ps := [cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB12 tailSupportB13 (by decide +kernel) rfl

private def tailMaskB11 : Nat := maskB11 ||| tailMaskB12
private theorem tailSupportB11 : Supported [cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB11 := by
  exact Supported.blocks_cons (p := cyclesB11) (ps := [cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB11 tailSupportB12 (by decide +kernel) rfl

private def tailMaskB10 : Nat := maskB10 ||| tailMaskB11
private theorem tailSupportB10 : Supported [cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB10 := by
  exact Supported.blocks_cons (p := cyclesB10) (ps := [cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB10 tailSupportB11 (by decide +kernel) rfl

private def tailMaskB9 : Nat := maskB9 ||| tailMaskB10
private theorem tailSupportB9 : Supported [cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB9 := by
  exact Supported.blocks_cons (p := cyclesB9) (ps := [cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB9 tailSupportB10 (by decide +kernel) rfl

private def tailMaskB8 : Nat := maskB8 ||| tailMaskB9
private theorem tailSupportB8 : Supported [cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB8 := by
  exact Supported.blocks_cons (p := cyclesB8) (ps := [cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB8 tailSupportB9 (by decide +kernel) rfl

private def tailMaskB7 : Nat := maskB7 ||| tailMaskB8
private theorem tailSupportB7 : Supported [cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB7 := by
  exact Supported.blocks_cons (p := cyclesB7) (ps := [cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB7 tailSupportB8 (by decide +kernel) rfl

private def tailMaskB6 : Nat := maskB6 ||| tailMaskB7
private theorem tailSupportB6 : Supported [cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB6 := by
  exact Supported.blocks_cons (p := cyclesB6) (ps := [cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB6 tailSupportB7 (by decide +kernel) rfl

private def tailMaskB5 : Nat := maskB5 ||| tailMaskB6
private theorem tailSupportB5 : Supported [cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB5 := by
  exact Supported.blocks_cons (p := cyclesB5) (ps := [cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB5 tailSupportB6 (by decide +kernel) rfl

private def tailMaskB4 : Nat := maskB4 ||| tailMaskB5
private theorem tailSupportB4 : Supported [cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB4 := by
  exact Supported.blocks_cons (p := cyclesB4) (ps := [cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB4 tailSupportB5 (by decide +kernel) rfl

private def tailMaskB3 : Nat := maskB3 ||| tailMaskB4
private theorem tailSupportB3 : Supported [cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB3 := by
  exact Supported.blocks_cons (p := cyclesB3) (ps := [cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB3 tailSupportB4 (by decide +kernel) rfl

private def tailMaskB2 : Nat := maskB2 ||| tailMaskB3
private theorem tailSupportB2 : Supported [cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB2 := by
  exact Supported.blocks_cons (p := cyclesB2) (ps := [cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB2 tailSupportB3 (by decide +kernel) rfl

private def tailMaskB1 : Nat := maskB1 ||| tailMaskB2
private theorem tailSupportB1 : Supported [cyclesB1, cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB1 := by
  exact Supported.blocks_cons (p := cyclesB1) (ps := [cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB1 tailSupportB2 (by decide +kernel) rfl

private def tailMaskB0 : Nat := maskB0 ||| tailMaskB1
private theorem tailSupportB0 : Supported [cyclesB0, cyclesB1, cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41].flatten.flatten tailMaskB0 := by
  exact Supported.blocks_cons (p := cyclesB0) (ps := [cyclesB1, cyclesB2, cyclesB3, cyclesB4, cyclesB5, cyclesB6, cyclesB7, cyclesB8, cyclesB9, cyclesB10, cyclesB11, cyclesB12, cyclesB13, cyclesB14, cyclesB15, cyclesB16, cyclesB17, cyclesB18, cyclesB19, cyclesB20, cyclesB21, cyclesB22, cyclesB23, cyclesB24, cyclesB25, cyclesB26, cyclesB27, cyclesB28, cyclesB29, cyclesB30, cyclesB31, cyclesB32, cyclesB33, cyclesB34, cyclesB35, cyclesB36, cyclesB37, cyclesB38, cyclesB39, cyclesB40, cyclesB41])
    supportB0 tailSupportB1 (by decide +kernel) rfl

theorem supportB : Supported cyclesB.flatten supportMaskB := by
  have hm : tailMaskB0 = supportMaskB := by decide +kernel
  exact hm ▸ tailSupportB0

theorem actionB :
    (cyclesB.all fun c => c.all fun x => decide (c.formPerm (bMap x) = x)) = true := by
  simp only [cyclesB, List.all_flatten, List.all_cons, List.all_nil,
    actionB0, actionB1, actionB2, actionB3, actionB4, actionB5, actionB6, actionB7, actionB8, actionB9, actionB10, actionB11, actionB12, actionB13, actionB14, actionB15, actionB16, actionB17, actionB18, actionB19, actionB20, actionB21, actionB22, actionB23, actionB24, actionB25, actionB26, actionB27, actionB28, actionB29, actionB30, actionB31, actionB32, actionB33, actionB34, actionB35, actionB36, actionB37, actionB38, actionB39, actionB40, actionB41, Bool.true_and]

end Sporadic.Fischer.Fi23.CentralizerSection.CandidateCertificate
