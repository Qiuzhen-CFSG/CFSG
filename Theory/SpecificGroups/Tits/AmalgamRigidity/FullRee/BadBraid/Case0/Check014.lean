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
private theorem checked_57344 : checkBoolChunk context facts instructions 57344 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_57856 : checkBoolChunk context facts instructions 57856 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_58368 : checkBoolChunk context facts instructions 58368 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_58880 : checkBoolChunk context facts instructions 58880 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_59392 : checkBoolChunk context facts instructions 59392 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_59904 : checkBoolChunk context facts instructions 59904 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_60416 : checkBoolChunk context facts instructions 60416 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_60928 : checkBoolChunk context facts instructions 60928 512 = true := by decide +kernel

theorem advance_57344 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 57344 → Holds H g ρ (facts n)) :
    ∀ n, n < 61440 → Holds H g ρ (facts n) := by
  have h57344 := checkBoolChunk_sound valid facts instructions 57344 512 prior checked_57344
  have h57856 := checkBoolChunk_sound valid facts instructions 57856 512 h57344 checked_57856
  have h58368 := checkBoolChunk_sound valid facts instructions 58368 512 h57856 checked_58368
  have h58880 := checkBoolChunk_sound valid facts instructions 58880 512 h58368 checked_58880
  have h59392 := checkBoolChunk_sound valid facts instructions 59392 512 h58880 checked_59392
  have h59904 := checkBoolChunk_sound valid facts instructions 59904 512 h59392 checked_59904
  have h60416 := checkBoolChunk_sound valid facts instructions 60416 512 h59904 checked_60416
  have h60928 := checkBoolChunk_sound valid facts instructions 60928 512 h60416 checked_60928
  exact h60928

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
