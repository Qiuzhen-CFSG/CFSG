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
private theorem checked_73728 : checkBoolChunk context facts instructions 73728 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_74240 : checkBoolChunk context facts instructions 74240 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_74752 : checkBoolChunk context facts instructions 74752 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_75264 : checkBoolChunk context facts instructions 75264 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_75776 : checkBoolChunk context facts instructions 75776 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_76288 : checkBoolChunk context facts instructions 76288 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_76800 : checkBoolChunk context facts instructions 76800 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_77312 : checkBoolChunk context facts instructions 77312 512 = true := by decide +kernel

theorem advance_73728 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 73728 → Holds H g ρ (facts n)) :
    ∀ n, n < 77824 → Holds H g ρ (facts n) := by
  have h73728 := checkBoolChunk_sound valid facts instructions 73728 512 prior checked_73728
  have h74240 := checkBoolChunk_sound valid facts instructions 74240 512 h73728 checked_74240
  have h74752 := checkBoolChunk_sound valid facts instructions 74752 512 h74240 checked_74752
  have h75264 := checkBoolChunk_sound valid facts instructions 75264 512 h74752 checked_75264
  have h75776 := checkBoolChunk_sound valid facts instructions 75776 512 h75264 checked_75776
  have h76288 := checkBoolChunk_sound valid facts instructions 76288 512 h75776 checked_76288
  have h76800 := checkBoolChunk_sound valid facts instructions 76800 512 h76288 checked_76800
  have h77312 := checkBoolChunk_sound valid facts instructions 77312 512 h76800 checked_77312
  exact h77312

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
