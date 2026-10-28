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
private theorem checked_32768 : checkBoolChunk context facts instructions 32768 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_33280 : checkBoolChunk context facts instructions 33280 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_33792 : checkBoolChunk context facts instructions 33792 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_34304 : checkBoolChunk context facts instructions 34304 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_34816 : checkBoolChunk context facts instructions 34816 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_35328 : checkBoolChunk context facts instructions 35328 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_35840 : checkBoolChunk context facts instructions 35840 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_36352 : checkBoolChunk context facts instructions 36352 512 = true := by decide +kernel

theorem advance_32768 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 32768 → Holds H g ρ (facts n)) :
    ∀ n, n < 36864 → Holds H g ρ (facts n) := by
  have h32768 := checkBoolChunk_sound valid facts instructions 32768 512 prior checked_32768
  have h33280 := checkBoolChunk_sound valid facts instructions 33280 512 h32768 checked_33280
  have h33792 := checkBoolChunk_sound valid facts instructions 33792 512 h33280 checked_33792
  have h34304 := checkBoolChunk_sound valid facts instructions 34304 512 h33792 checked_34304
  have h34816 := checkBoolChunk_sound valid facts instructions 34816 512 h34304 checked_34816
  have h35328 := checkBoolChunk_sound valid facts instructions 35328 512 h34816 checked_35328
  have h35840 := checkBoolChunk_sound valid facts instructions 35840 512 h35328 checked_35840
  have h36352 := checkBoolChunk_sound valid facts instructions 36352 512 h35840 checked_36352
  exact h36352

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
