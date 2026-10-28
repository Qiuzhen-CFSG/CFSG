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
private theorem checked_4096 : checkBoolChunk context facts instructions 4096 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_4608 : checkBoolChunk context facts instructions 4608 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_5120 : checkBoolChunk context facts instructions 5120 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_5632 : checkBoolChunk context facts instructions 5632 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_6144 : checkBoolChunk context facts instructions 6144 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_6656 : checkBoolChunk context facts instructions 6656 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_7168 : checkBoolChunk context facts instructions 7168 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_7680 : checkBoolChunk context facts instructions 7680 512 = true := by decide +kernel

theorem advance_4096 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 4096 → Holds H g ρ (facts n)) :
    ∀ n, n < 8192 → Holds H g ρ (facts n) := by
  have h4096 := checkBoolChunk_sound valid facts instructions 4096 512 prior checked_4096
  have h4608 := checkBoolChunk_sound valid facts instructions 4608 512 h4096 checked_4608
  have h5120 := checkBoolChunk_sound valid facts instructions 5120 512 h4608 checked_5120
  have h5632 := checkBoolChunk_sound valid facts instructions 5632 512 h5120 checked_5632
  have h6144 := checkBoolChunk_sound valid facts instructions 6144 512 h5632 checked_6144
  have h6656 := checkBoolChunk_sound valid facts instructions 6656 512 h6144 checked_6656
  have h7168 := checkBoolChunk_sound valid facts instructions 7168 512 h6656 checked_7168
  have h7680 := checkBoolChunk_sound valid facts instructions 7680 512 h7168 checked_7680
  exact h7680

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
