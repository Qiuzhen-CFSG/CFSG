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
private theorem checked_155648 : checkBoolChunk context facts instructions 155648 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_156160 : checkBoolChunk context facts instructions 156160 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_156672 : checkBoolChunk context facts instructions 156672 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_157184 : checkBoolChunk context facts instructions 157184 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_157696 : checkBoolChunk context facts instructions 157696 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_158208 : checkBoolChunk context facts instructions 158208 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_158720 : checkBoolChunk context facts instructions 158720 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_159232 : checkBoolChunk context facts instructions 159232 512 = true := by decide +kernel

theorem advance_155648 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 155648 → Holds H g ρ (facts n)) :
    ∀ n, n < 159744 → Holds H g ρ (facts n) := by
  have h155648 := checkBoolChunk_sound valid facts instructions 155648 512 prior checked_155648
  have h156160 := checkBoolChunk_sound valid facts instructions 156160 512 h155648 checked_156160
  have h156672 := checkBoolChunk_sound valid facts instructions 156672 512 h156160 checked_156672
  have h157184 := checkBoolChunk_sound valid facts instructions 157184 512 h156672 checked_157184
  have h157696 := checkBoolChunk_sound valid facts instructions 157696 512 h157184 checked_157696
  have h158208 := checkBoolChunk_sound valid facts instructions 158208 512 h157696 checked_158208
  have h158720 := checkBoolChunk_sound valid facts instructions 158720 512 h158208 checked_158720
  have h159232 := checkBoolChunk_sound valid facts instructions 159232 512 h158720 checked_159232
  exact h159232

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
