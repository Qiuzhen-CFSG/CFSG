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
private theorem checked_24576 : checkBoolChunk context facts instructions 24576 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_25088 : checkBoolChunk context facts instructions 25088 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_25600 : checkBoolChunk context facts instructions 25600 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_26112 : checkBoolChunk context facts instructions 26112 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_26624 : checkBoolChunk context facts instructions 26624 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_27136 : checkBoolChunk context facts instructions 27136 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_27648 : checkBoolChunk context facts instructions 27648 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_28160 : checkBoolChunk context facts instructions 28160 512 = true := by decide +kernel

theorem advance_24576 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 24576 → Holds H g ρ (facts n)) :
    ∀ n, n < 28672 → Holds H g ρ (facts n) := by
  have h24576 := checkBoolChunk_sound valid facts instructions 24576 512 prior checked_24576
  have h25088 := checkBoolChunk_sound valid facts instructions 25088 512 h24576 checked_25088
  have h25600 := checkBoolChunk_sound valid facts instructions 25600 512 h25088 checked_25600
  have h26112 := checkBoolChunk_sound valid facts instructions 26112 512 h25600 checked_26112
  have h26624 := checkBoolChunk_sound valid facts instructions 26624 512 h26112 checked_26624
  have h27136 := checkBoolChunk_sound valid facts instructions 27136 512 h26624 checked_27136
  have h27648 := checkBoolChunk_sound valid facts instructions 27648 512 h27136 checked_27648
  have h28160 := checkBoolChunk_sound valid facts instructions 28160 512 h27648 checked_28160
  exact h28160

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
