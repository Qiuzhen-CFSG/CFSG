module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case1.Context
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case1.Data

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case1
open Subgroup.CosetWordCertificate
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem checked_86016 : checkBoolChunk context facts instructions 86016 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_86528 : checkBoolChunk context facts instructions 86528 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_87040 : checkBoolChunk context facts instructions 87040 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_87552 : checkBoolChunk context facts instructions 87552 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_88064 : checkBoolChunk context facts instructions 88064 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_88576 : checkBoolChunk context facts instructions 88576 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_89088 : checkBoolChunk context facts instructions 89088 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_89600 : checkBoolChunk context facts instructions 89600 512 = true := by decide +kernel

theorem advance_86016 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 86016 → Holds H g ρ (facts n)) :
    ∀ n, n < 90112 → Holds H g ρ (facts n) := by
  have h86016 := checkBoolChunk_sound valid facts instructions 86016 512 prior checked_86016
  have h86528 := checkBoolChunk_sound valid facts instructions 86528 512 h86016 checked_86528
  have h87040 := checkBoolChunk_sound valid facts instructions 87040 512 h86528 checked_87040
  have h87552 := checkBoolChunk_sound valid facts instructions 87552 512 h87040 checked_87552
  have h88064 := checkBoolChunk_sound valid facts instructions 88064 512 h87552 checked_88064
  have h88576 := checkBoolChunk_sound valid facts instructions 88576 512 h88064 checked_88576
  have h89088 := checkBoolChunk_sound valid facts instructions 89088 512 h88576 checked_89088
  have h89600 := checkBoolChunk_sound valid facts instructions 89600 512 h89088 checked_89600
  exact h89600

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
