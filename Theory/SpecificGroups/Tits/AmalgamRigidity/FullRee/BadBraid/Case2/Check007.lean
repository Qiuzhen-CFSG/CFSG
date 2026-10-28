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
private theorem checked_28672 : checkBoolChunk context facts instructions 28672 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_29184 : checkBoolChunk context facts instructions 29184 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_29696 : checkBoolChunk context facts instructions 29696 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_30208 : checkBoolChunk context facts instructions 30208 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_30720 : checkBoolChunk context facts instructions 30720 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_31232 : checkBoolChunk context facts instructions 31232 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_31744 : checkBoolChunk context facts instructions 31744 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_32256 : checkBoolChunk context facts instructions 32256 512 = true := by decide +kernel

theorem advance_28672 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 28672 → Holds H g ρ (facts n)) :
    ∀ n, n < 32768 → Holds H g ρ (facts n) := by
  have h28672 := checkBoolChunk_sound valid facts instructions 28672 512 prior checked_28672
  have h29184 := checkBoolChunk_sound valid facts instructions 29184 512 h28672 checked_29184
  have h29696 := checkBoolChunk_sound valid facts instructions 29696 512 h29184 checked_29696
  have h30208 := checkBoolChunk_sound valid facts instructions 30208 512 h29696 checked_30208
  have h30720 := checkBoolChunk_sound valid facts instructions 30720 512 h30208 checked_30720
  have h31232 := checkBoolChunk_sound valid facts instructions 31232 512 h30720 checked_31232
  have h31744 := checkBoolChunk_sound valid facts instructions 31744 512 h31232 checked_31744
  have h32256 := checkBoolChunk_sound valid facts instructions 32256 512 h31744 checked_32256
  exact h32256

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
