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
private theorem checked_118784 : checkBoolChunk context facts instructions 118784 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_119296 : checkBoolChunk context facts instructions 119296 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_119808 : checkBoolChunk context facts instructions 119808 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_120320 : checkBoolChunk context facts instructions 120320 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_120832 : checkBoolChunk context facts instructions 120832 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_121344 : checkBoolChunk context facts instructions 121344 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_121856 : checkBoolChunk context facts instructions 121856 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_122368 : checkBoolChunk context facts instructions 122368 512 = true := by decide +kernel

theorem advance_118784 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 118784 → Holds H g ρ (facts n)) :
    ∀ n, n < 122880 → Holds H g ρ (facts n) := by
  have h118784 := checkBoolChunk_sound valid facts instructions 118784 512 prior checked_118784
  have h119296 := checkBoolChunk_sound valid facts instructions 119296 512 h118784 checked_119296
  have h119808 := checkBoolChunk_sound valid facts instructions 119808 512 h119296 checked_119808
  have h120320 := checkBoolChunk_sound valid facts instructions 120320 512 h119808 checked_120320
  have h120832 := checkBoolChunk_sound valid facts instructions 120832 512 h120320 checked_120832
  have h121344 := checkBoolChunk_sound valid facts instructions 121344 512 h120832 checked_121344
  have h121856 := checkBoolChunk_sound valid facts instructions 121856 512 h121344 checked_121856
  have h122368 := checkBoolChunk_sound valid facts instructions 122368 512 h121856 checked_122368
  exact h122368

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
