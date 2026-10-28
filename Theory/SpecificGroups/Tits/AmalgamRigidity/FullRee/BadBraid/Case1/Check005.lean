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
private theorem checked_20480 : checkBoolChunk context facts instructions 20480 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_20992 : checkBoolChunk context facts instructions 20992 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_21504 : checkBoolChunk context facts instructions 21504 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_22016 : checkBoolChunk context facts instructions 22016 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_22528 : checkBoolChunk context facts instructions 22528 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_23040 : checkBoolChunk context facts instructions 23040 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_23552 : checkBoolChunk context facts instructions 23552 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_24064 : checkBoolChunk context facts instructions 24064 512 = true := by decide +kernel

theorem advance_20480 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 20480 → Holds H g ρ (facts n)) :
    ∀ n, n < 24576 → Holds H g ρ (facts n) := by
  have h20480 := checkBoolChunk_sound valid facts instructions 20480 512 prior checked_20480
  have h20992 := checkBoolChunk_sound valid facts instructions 20992 512 h20480 checked_20992
  have h21504 := checkBoolChunk_sound valid facts instructions 21504 512 h20992 checked_21504
  have h22016 := checkBoolChunk_sound valid facts instructions 22016 512 h21504 checked_22016
  have h22528 := checkBoolChunk_sound valid facts instructions 22528 512 h22016 checked_22528
  have h23040 := checkBoolChunk_sound valid facts instructions 23040 512 h22528 checked_23040
  have h23552 := checkBoolChunk_sound valid facts instructions 23552 512 h23040 checked_23552
  have h24064 := checkBoolChunk_sound valid facts instructions 24064 512 h23552 checked_24064
  exact h24064

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
