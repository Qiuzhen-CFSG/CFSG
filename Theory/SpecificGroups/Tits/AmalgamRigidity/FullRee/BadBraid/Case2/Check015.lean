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
private theorem checked_61440 : checkBoolChunk context facts instructions 61440 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_61952 : checkBoolChunk context facts instructions 61952 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_62464 : checkBoolChunk context facts instructions 62464 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_62976 : checkBoolChunk context facts instructions 62976 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_63488 : checkBoolChunk context facts instructions 63488 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_64000 : checkBoolChunk context facts instructions 64000 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_64512 : checkBoolChunk context facts instructions 64512 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_65024 : checkBoolChunk context facts instructions 65024 512 = true := by decide +kernel

theorem advance_61440 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 61440 → Holds H g ρ (facts n)) :
    ∀ n, n < 65536 → Holds H g ρ (facts n) := by
  have h61440 := checkBoolChunk_sound valid facts instructions 61440 512 prior checked_61440
  have h61952 := checkBoolChunk_sound valid facts instructions 61952 512 h61440 checked_61952
  have h62464 := checkBoolChunk_sound valid facts instructions 62464 512 h61952 checked_62464
  have h62976 := checkBoolChunk_sound valid facts instructions 62976 512 h62464 checked_62976
  have h63488 := checkBoolChunk_sound valid facts instructions 63488 512 h62976 checked_63488
  have h64000 := checkBoolChunk_sound valid facts instructions 64000 512 h63488 checked_64000
  have h64512 := checkBoolChunk_sound valid facts instructions 64512 512 h64000 checked_64512
  have h65024 := checkBoolChunk_sound valid facts instructions 65024 512 h64512 checked_65024
  exact h65024

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
