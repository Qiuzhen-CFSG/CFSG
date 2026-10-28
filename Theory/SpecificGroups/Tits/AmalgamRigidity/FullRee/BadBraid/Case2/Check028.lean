module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Context
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Data

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case2
open Subgroup.CosetWordCertificate
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem checked_114688 : checkBoolChunk context facts instructions 114688 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_115200 : checkBoolChunk context facts instructions 115200 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_115712 : checkBoolChunk context facts instructions 115712 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_116224 : checkBoolChunk context facts instructions 116224 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_116736 : checkBoolChunk context facts instructions 116736 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_117248 : checkBoolChunk context facts instructions 117248 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_117760 : checkBoolChunk context facts instructions 117760 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_118272 : checkBoolChunk context facts instructions 118272 512 = true := by decide +kernel

theorem advance_114688 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 114688 → Holds H g ρ (facts n)) :
    ∀ n, n < 118784 → Holds H g ρ (facts n) := by
  have h114688 := checkBoolChunk_sound valid facts instructions 114688 512 prior checked_114688
  have h115200 := checkBoolChunk_sound valid facts instructions 115200 512 h114688 checked_115200
  have h115712 := checkBoolChunk_sound valid facts instructions 115712 512 h115200 checked_115712
  have h116224 := checkBoolChunk_sound valid facts instructions 116224 512 h115712 checked_116224
  have h116736 := checkBoolChunk_sound valid facts instructions 116736 512 h116224 checked_116736
  have h117248 := checkBoolChunk_sound valid facts instructions 117248 512 h116736 checked_117248
  have h117760 := checkBoolChunk_sound valid facts instructions 117760 512 h117248 checked_117760
  have h118272 := checkBoolChunk_sound valid facts instructions 118272 512 h117760 checked_118272
  exact h118272

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
