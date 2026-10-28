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
private theorem checked_8192 : checkBoolChunk context facts instructions 8192 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_8704 : checkBoolChunk context facts instructions 8704 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_9216 : checkBoolChunk context facts instructions 9216 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_9728 : checkBoolChunk context facts instructions 9728 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_10240 : checkBoolChunk context facts instructions 10240 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_10752 : checkBoolChunk context facts instructions 10752 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_11264 : checkBoolChunk context facts instructions 11264 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_11776 : checkBoolChunk context facts instructions 11776 512 = true := by decide +kernel

theorem advance_8192 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 8192 → Holds H g ρ (facts n)) :
    ∀ n, n < 12288 → Holds H g ρ (facts n) := by
  have h8192 := checkBoolChunk_sound valid facts instructions 8192 512 prior checked_8192
  have h8704 := checkBoolChunk_sound valid facts instructions 8704 512 h8192 checked_8704
  have h9216 := checkBoolChunk_sound valid facts instructions 9216 512 h8704 checked_9216
  have h9728 := checkBoolChunk_sound valid facts instructions 9728 512 h9216 checked_9728
  have h10240 := checkBoolChunk_sound valid facts instructions 10240 512 h9728 checked_10240
  have h10752 := checkBoolChunk_sound valid facts instructions 10752 512 h10240 checked_10752
  have h11264 := checkBoolChunk_sound valid facts instructions 11264 512 h10752 checked_11264
  have h11776 := checkBoolChunk_sound valid facts instructions 11776 512 h11264 checked_11776
  exact h11776

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
