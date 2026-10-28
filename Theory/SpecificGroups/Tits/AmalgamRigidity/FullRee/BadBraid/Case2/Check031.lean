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
private theorem checked_126976 : checkBoolChunk context facts instructions 126976 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_127488 : checkBoolChunk context facts instructions 127488 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_128000 : checkBoolChunk context facts instructions 128000 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_128512 : checkBoolChunk context facts instructions 128512 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_129024 : checkBoolChunk context facts instructions 129024 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_129536 : checkBoolChunk context facts instructions 129536 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_130048 : checkBoolChunk context facts instructions 130048 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_130560 : checkBoolChunk context facts instructions 130560 512 = true := by decide +kernel

theorem advance_126976 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 126976 → Holds H g ρ (facts n)) :
    ∀ n, n < 131072 → Holds H g ρ (facts n) := by
  have h126976 := checkBoolChunk_sound valid facts instructions 126976 512 prior checked_126976
  have h127488 := checkBoolChunk_sound valid facts instructions 127488 512 h126976 checked_127488
  have h128000 := checkBoolChunk_sound valid facts instructions 128000 512 h127488 checked_128000
  have h128512 := checkBoolChunk_sound valid facts instructions 128512 512 h128000 checked_128512
  have h129024 := checkBoolChunk_sound valid facts instructions 129024 512 h128512 checked_129024
  have h129536 := checkBoolChunk_sound valid facts instructions 129536 512 h129024 checked_129536
  have h130048 := checkBoolChunk_sound valid facts instructions 130048 512 h129536 checked_130048
  have h130560 := checkBoolChunk_sound valid facts instructions 130560 512 h130048 checked_130560
  exact h130560

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
