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
private theorem checked_36864 : checkBoolChunk context facts instructions 36864 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_37376 : checkBoolChunk context facts instructions 37376 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_37888 : checkBoolChunk context facts instructions 37888 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_38400 : checkBoolChunk context facts instructions 38400 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_38912 : checkBoolChunk context facts instructions 38912 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_39424 : checkBoolChunk context facts instructions 39424 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_39936 : checkBoolChunk context facts instructions 39936 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_40448 : checkBoolChunk context facts instructions 40448 512 = true := by decide +kernel

theorem advance_36864 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 36864 → Holds H g ρ (facts n)) :
    ∀ n, n < 40960 → Holds H g ρ (facts n) := by
  have h36864 := checkBoolChunk_sound valid facts instructions 36864 512 prior checked_36864
  have h37376 := checkBoolChunk_sound valid facts instructions 37376 512 h36864 checked_37376
  have h37888 := checkBoolChunk_sound valid facts instructions 37888 512 h37376 checked_37888
  have h38400 := checkBoolChunk_sound valid facts instructions 38400 512 h37888 checked_38400
  have h38912 := checkBoolChunk_sound valid facts instructions 38912 512 h38400 checked_38912
  have h39424 := checkBoolChunk_sound valid facts instructions 39424 512 h38912 checked_39424
  have h39936 := checkBoolChunk_sound valid facts instructions 39936 512 h39424 checked_39936
  have h40448 := checkBoolChunk_sound valid facts instructions 40448 512 h39936 checked_40448
  exact h40448

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
