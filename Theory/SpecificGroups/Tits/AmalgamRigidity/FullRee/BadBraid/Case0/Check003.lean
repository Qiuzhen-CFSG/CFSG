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
private theorem checked_12288 : checkBoolChunk context facts instructions 12288 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_12800 : checkBoolChunk context facts instructions 12800 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_13312 : checkBoolChunk context facts instructions 13312 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_13824 : checkBoolChunk context facts instructions 13824 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_14336 : checkBoolChunk context facts instructions 14336 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_14848 : checkBoolChunk context facts instructions 14848 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_15360 : checkBoolChunk context facts instructions 15360 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_15872 : checkBoolChunk context facts instructions 15872 512 = true := by decide +kernel

theorem advance_12288 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 12288 → Holds H g ρ (facts n)) :
    ∀ n, n < 16384 → Holds H g ρ (facts n) := by
  have h12288 := checkBoolChunk_sound valid facts instructions 12288 512 prior checked_12288
  have h12800 := checkBoolChunk_sound valid facts instructions 12800 512 h12288 checked_12800
  have h13312 := checkBoolChunk_sound valid facts instructions 13312 512 h12800 checked_13312
  have h13824 := checkBoolChunk_sound valid facts instructions 13824 512 h13312 checked_13824
  have h14336 := checkBoolChunk_sound valid facts instructions 14336 512 h13824 checked_14336
  have h14848 := checkBoolChunk_sound valid facts instructions 14848 512 h14336 checked_14848
  have h15360 := checkBoolChunk_sound valid facts instructions 15360 512 h14848 checked_15360
  have h15872 := checkBoolChunk_sound valid facts instructions 15872 512 h15360 checked_15872
  exact h15872

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
