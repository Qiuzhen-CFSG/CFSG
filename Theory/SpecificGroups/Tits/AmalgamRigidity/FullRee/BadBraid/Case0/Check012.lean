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
private theorem checked_49152 : checkBoolChunk context facts instructions 49152 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_49664 : checkBoolChunk context facts instructions 49664 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_50176 : checkBoolChunk context facts instructions 50176 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_50688 : checkBoolChunk context facts instructions 50688 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_51200 : checkBoolChunk context facts instructions 51200 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_51712 : checkBoolChunk context facts instructions 51712 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_52224 : checkBoolChunk context facts instructions 52224 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_52736 : checkBoolChunk context facts instructions 52736 512 = true := by decide +kernel

theorem advance_49152 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 49152 → Holds H g ρ (facts n)) :
    ∀ n, n < 53248 → Holds H g ρ (facts n) := by
  have h49152 := checkBoolChunk_sound valid facts instructions 49152 512 prior checked_49152
  have h49664 := checkBoolChunk_sound valid facts instructions 49664 512 h49152 checked_49664
  have h50176 := checkBoolChunk_sound valid facts instructions 50176 512 h49664 checked_50176
  have h50688 := checkBoolChunk_sound valid facts instructions 50688 512 h50176 checked_50688
  have h51200 := checkBoolChunk_sound valid facts instructions 51200 512 h50688 checked_51200
  have h51712 := checkBoolChunk_sound valid facts instructions 51712 512 h51200 checked_51712
  have h52224 := checkBoolChunk_sound valid facts instructions 52224 512 h51712 checked_52224
  have h52736 := checkBoolChunk_sound valid facts instructions 52736 512 h52224 checked_52736
  exact h52736

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
