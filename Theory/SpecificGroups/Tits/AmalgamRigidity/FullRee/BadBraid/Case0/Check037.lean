module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.Context
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case0.Data

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case0
open Subgroup.CosetWordCertificate
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem checked_151552 : checkBoolChunk context facts instructions 151552 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_152064 : checkBoolChunk context facts instructions 152064 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_152576 : checkBoolChunk context facts instructions 152576 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_153088 : checkBoolChunk context facts instructions 153088 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_153600 : checkBoolChunk context facts instructions 153600 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_154112 : checkBoolChunk context facts instructions 154112 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_154624 : checkBoolChunk context facts instructions 154624 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_155136 : checkBoolChunk context facts instructions 155136 512 = true := by decide +kernel

theorem advance_151552 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 151552 → Holds H g ρ (facts n)) :
    ∀ n, n < 155648 → Holds H g ρ (facts n) := by
  have h151552 := checkBoolChunk_sound valid facts instructions 151552 512 prior checked_151552
  have h152064 := checkBoolChunk_sound valid facts instructions 152064 512 h151552 checked_152064
  have h152576 := checkBoolChunk_sound valid facts instructions 152576 512 h152064 checked_152576
  have h153088 := checkBoolChunk_sound valid facts instructions 153088 512 h152576 checked_153088
  have h153600 := checkBoolChunk_sound valid facts instructions 153600 512 h153088 checked_153600
  have h154112 := checkBoolChunk_sound valid facts instructions 154112 512 h153600 checked_154112
  have h154624 := checkBoolChunk_sound valid facts instructions 154624 512 h154112 checked_154624
  have h155136 := checkBoolChunk_sound valid facts instructions 155136 512 h154624 checked_155136
  exact h155136

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
