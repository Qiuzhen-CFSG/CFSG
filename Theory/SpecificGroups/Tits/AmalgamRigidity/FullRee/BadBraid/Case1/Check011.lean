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
private theorem checked_45056 : checkBoolChunk context facts instructions 45056 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_45568 : checkBoolChunk context facts instructions 45568 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_46080 : checkBoolChunk context facts instructions 46080 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_46592 : checkBoolChunk context facts instructions 46592 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_47104 : checkBoolChunk context facts instructions 47104 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_47616 : checkBoolChunk context facts instructions 47616 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_48128 : checkBoolChunk context facts instructions 48128 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_48640 : checkBoolChunk context facts instructions 48640 512 = true := by decide +kernel

theorem advance_45056 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 45056 → Holds H g ρ (facts n)) :
    ∀ n, n < 49152 → Holds H g ρ (facts n) := by
  have h45056 := checkBoolChunk_sound valid facts instructions 45056 512 prior checked_45056
  have h45568 := checkBoolChunk_sound valid facts instructions 45568 512 h45056 checked_45568
  have h46080 := checkBoolChunk_sound valid facts instructions 46080 512 h45568 checked_46080
  have h46592 := checkBoolChunk_sound valid facts instructions 46592 512 h46080 checked_46592
  have h47104 := checkBoolChunk_sound valid facts instructions 47104 512 h46592 checked_47104
  have h47616 := checkBoolChunk_sound valid facts instructions 47616 512 h47104 checked_47616
  have h48128 := checkBoolChunk_sound valid facts instructions 48128 512 h47616 checked_48128
  have h48640 := checkBoolChunk_sound valid facts instructions 48640 512 h48128 checked_48640
  exact h48640

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
