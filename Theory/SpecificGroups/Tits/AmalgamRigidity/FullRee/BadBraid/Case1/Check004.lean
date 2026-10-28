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
private theorem checked_16384 : checkBoolChunk context facts instructions 16384 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_16896 : checkBoolChunk context facts instructions 16896 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_17408 : checkBoolChunk context facts instructions 17408 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_17920 : checkBoolChunk context facts instructions 17920 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_18432 : checkBoolChunk context facts instructions 18432 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_18944 : checkBoolChunk context facts instructions 18944 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_19456 : checkBoolChunk context facts instructions 19456 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_19968 : checkBoolChunk context facts instructions 19968 512 = true := by decide +kernel

theorem advance_16384 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 16384 → Holds H g ρ (facts n)) :
    ∀ n, n < 20480 → Holds H g ρ (facts n) := by
  have h16384 := checkBoolChunk_sound valid facts instructions 16384 512 prior checked_16384
  have h16896 := checkBoolChunk_sound valid facts instructions 16896 512 h16384 checked_16896
  have h17408 := checkBoolChunk_sound valid facts instructions 17408 512 h16896 checked_17408
  have h17920 := checkBoolChunk_sound valid facts instructions 17920 512 h17408 checked_17920
  have h18432 := checkBoolChunk_sound valid facts instructions 18432 512 h17920 checked_18432
  have h18944 := checkBoolChunk_sound valid facts instructions 18944 512 h18432 checked_18944
  have h19456 := checkBoolChunk_sound valid facts instructions 19456 512 h18944 checked_19456
  have h19968 := checkBoolChunk_sound valid facts instructions 19968 512 h19456 checked_19968
  exact h19968

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
