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
private theorem checked_94208 : checkBoolChunk context facts instructions 94208 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_94720 : checkBoolChunk context facts instructions 94720 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_95232 : checkBoolChunk context facts instructions 95232 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_95744 : checkBoolChunk context facts instructions 95744 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_96256 : checkBoolChunk context facts instructions 96256 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_96768 : checkBoolChunk context facts instructions 96768 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_97280 : checkBoolChunk context facts instructions 97280 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_97792 : checkBoolChunk context facts instructions 97792 512 = true := by decide +kernel

theorem advance_94208 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 94208 → Holds H g ρ (facts n)) :
    ∀ n, n < 98304 → Holds H g ρ (facts n) := by
  have h94208 := checkBoolChunk_sound valid facts instructions 94208 512 prior checked_94208
  have h94720 := checkBoolChunk_sound valid facts instructions 94720 512 h94208 checked_94720
  have h95232 := checkBoolChunk_sound valid facts instructions 95232 512 h94720 checked_95232
  have h95744 := checkBoolChunk_sound valid facts instructions 95744 512 h95232 checked_95744
  have h96256 := checkBoolChunk_sound valid facts instructions 96256 512 h95744 checked_96256
  have h96768 := checkBoolChunk_sound valid facts instructions 96768 512 h96256 checked_96768
  have h97280 := checkBoolChunk_sound valid facts instructions 97280 512 h96768 checked_97280
  have h97792 := checkBoolChunk_sound valid facts instructions 97792 512 h97280 checked_97792
  exact h97792

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
