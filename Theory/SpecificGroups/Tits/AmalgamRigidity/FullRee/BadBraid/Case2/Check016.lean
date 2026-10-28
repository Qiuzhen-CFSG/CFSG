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
private theorem checked_65536 : checkBoolChunk context facts instructions 65536 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_66048 : checkBoolChunk context facts instructions 66048 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_66560 : checkBoolChunk context facts instructions 66560 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_67072 : checkBoolChunk context facts instructions 67072 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_67584 : checkBoolChunk context facts instructions 67584 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_68096 : checkBoolChunk context facts instructions 68096 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_68608 : checkBoolChunk context facts instructions 68608 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_69120 : checkBoolChunk context facts instructions 69120 512 = true := by decide +kernel

theorem advance_65536 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 65536 → Holds H g ρ (facts n)) :
    ∀ n, n < 69632 → Holds H g ρ (facts n) := by
  have h65536 := checkBoolChunk_sound valid facts instructions 65536 512 prior checked_65536
  have h66048 := checkBoolChunk_sound valid facts instructions 66048 512 h65536 checked_66048
  have h66560 := checkBoolChunk_sound valid facts instructions 66560 512 h66048 checked_66560
  have h67072 := checkBoolChunk_sound valid facts instructions 67072 512 h66560 checked_67072
  have h67584 := checkBoolChunk_sound valid facts instructions 67584 512 h67072 checked_67584
  have h68096 := checkBoolChunk_sound valid facts instructions 68096 512 h67584 checked_68096
  have h68608 := checkBoolChunk_sound valid facts instructions 68608 512 h68096 checked_68608
  have h69120 := checkBoolChunk_sound valid facts instructions 69120 512 h68608 checked_69120
  exact h69120

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
