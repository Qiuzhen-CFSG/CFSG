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
private theorem checked_180224 : checkBoolChunk context facts instructions 180224 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_180736 : checkBoolChunk context facts instructions 180736 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_181248 : checkBoolChunk context facts instructions 181248 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_181760 : checkBoolChunk context facts instructions 181760 151 = true := by decide +kernel

theorem advance_180224 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 180224 → Holds H g ρ (facts n)) :
    ∀ n, n < 181911 → Holds H g ρ (facts n) := by
  have h180224 := checkBoolChunk_sound valid facts instructions 180224 512 prior checked_180224
  have h180736 := checkBoolChunk_sound valid facts instructions 180736 512 h180224 checked_180736
  have h181248 := checkBoolChunk_sound valid facts instructions 181248 512 h180736 checked_181248
  have h181760 := checkBoolChunk_sound valid facts instructions 181760 151 h181248 checked_181760
  exact h181760

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
