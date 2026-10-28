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
private theorem checked_102400 : checkBoolChunk context facts instructions 102400 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_102912 : checkBoolChunk context facts instructions 102912 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_103424 : checkBoolChunk context facts instructions 103424 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_103936 : checkBoolChunk context facts instructions 103936 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_104448 : checkBoolChunk context facts instructions 104448 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_104960 : checkBoolChunk context facts instructions 104960 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_105472 : checkBoolChunk context facts instructions 105472 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_105984 : checkBoolChunk context facts instructions 105984 512 = true := by decide +kernel

theorem advance_102400 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 102400 → Holds H g ρ (facts n)) :
    ∀ n, n < 106496 → Holds H g ρ (facts n) := by
  have h102400 := checkBoolChunk_sound valid facts instructions 102400 512 prior checked_102400
  have h102912 := checkBoolChunk_sound valid facts instructions 102912 512 h102400 checked_102912
  have h103424 := checkBoolChunk_sound valid facts instructions 103424 512 h102912 checked_103424
  have h103936 := checkBoolChunk_sound valid facts instructions 103936 512 h103424 checked_103936
  have h104448 := checkBoolChunk_sound valid facts instructions 104448 512 h103936 checked_104448
  have h104960 := checkBoolChunk_sound valid facts instructions 104960 512 h104448 checked_104960
  have h105472 := checkBoolChunk_sound valid facts instructions 105472 512 h104960 checked_105472
  have h105984 := checkBoolChunk_sound valid facts instructions 105984 512 h105472 checked_105984
  exact h105984

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
