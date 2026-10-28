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
private theorem checked_0 : checkBoolChunk context facts instructions 0 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_512 : checkBoolChunk context facts instructions 512 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_1024 : checkBoolChunk context facts instructions 1024 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_1536 : checkBoolChunk context facts instructions 1536 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_2048 : checkBoolChunk context facts instructions 2048 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_2560 : checkBoolChunk context facts instructions 2560 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_3072 : checkBoolChunk context facts instructions 3072 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_3584 : checkBoolChunk context facts instructions 3584 512 = true := by decide +kernel

theorem advance_0 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 0 → Holds H g ρ (facts n)) :
    ∀ n, n < 4096 → Holds H g ρ (facts n) := by
  have h0 := checkBoolChunk_sound valid facts instructions 0 512 prior checked_0
  have h512 := checkBoolChunk_sound valid facts instructions 512 512 h0 checked_512
  have h1024 := checkBoolChunk_sound valid facts instructions 1024 512 h512 checked_1024
  have h1536 := checkBoolChunk_sound valid facts instructions 1536 512 h1024 checked_1536
  have h2048 := checkBoolChunk_sound valid facts instructions 2048 512 h1536 checked_2048
  have h2560 := checkBoolChunk_sound valid facts instructions 2560 512 h2048 checked_2560
  have h3072 := checkBoolChunk_sound valid facts instructions 3072 512 h2560 checked_3072
  have h3584 := checkBoolChunk_sound valid facts instructions 3584 512 h3072 checked_3584
  exact h3584

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
