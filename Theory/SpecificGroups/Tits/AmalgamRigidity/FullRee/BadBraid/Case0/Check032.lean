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
private theorem checked_131072 : checkBoolChunk context facts instructions 131072 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_131584 : checkBoolChunk context facts instructions 131584 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_132096 : checkBoolChunk context facts instructions 132096 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_132608 : checkBoolChunk context facts instructions 132608 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_133120 : checkBoolChunk context facts instructions 133120 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_133632 : checkBoolChunk context facts instructions 133632 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_134144 : checkBoolChunk context facts instructions 134144 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_134656 : checkBoolChunk context facts instructions 134656 512 = true := by decide +kernel

theorem advance_131072 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 131072 → Holds H g ρ (facts n)) :
    ∀ n, n < 135168 → Holds H g ρ (facts n) := by
  have h131072 := checkBoolChunk_sound valid facts instructions 131072 512 prior checked_131072
  have h131584 := checkBoolChunk_sound valid facts instructions 131584 512 h131072 checked_131584
  have h132096 := checkBoolChunk_sound valid facts instructions 132096 512 h131584 checked_132096
  have h132608 := checkBoolChunk_sound valid facts instructions 132608 512 h132096 checked_132608
  have h133120 := checkBoolChunk_sound valid facts instructions 133120 512 h132608 checked_133120
  have h133632 := checkBoolChunk_sound valid facts instructions 133632 512 h133120 checked_133632
  have h134144 := checkBoolChunk_sound valid facts instructions 134144 512 h133632 checked_134144
  have h134656 := checkBoolChunk_sound valid facts instructions 134656 512 h134144 checked_134656
  exact h134656

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
