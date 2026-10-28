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
private theorem checked_40960 : checkBoolChunk context facts instructions 40960 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_41472 : checkBoolChunk context facts instructions 41472 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_41984 : checkBoolChunk context facts instructions 41984 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_42496 : checkBoolChunk context facts instructions 42496 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_43008 : checkBoolChunk context facts instructions 43008 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_43520 : checkBoolChunk context facts instructions 43520 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_44032 : checkBoolChunk context facts instructions 44032 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_44544 : checkBoolChunk context facts instructions 44544 512 = true := by decide +kernel

theorem advance_40960 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 40960 → Holds H g ρ (facts n)) :
    ∀ n, n < 45056 → Holds H g ρ (facts n) := by
  have h40960 := checkBoolChunk_sound valid facts instructions 40960 512 prior checked_40960
  have h41472 := checkBoolChunk_sound valid facts instructions 41472 512 h40960 checked_41472
  have h41984 := checkBoolChunk_sound valid facts instructions 41984 512 h41472 checked_41984
  have h42496 := checkBoolChunk_sound valid facts instructions 42496 512 h41984 checked_42496
  have h43008 := checkBoolChunk_sound valid facts instructions 43008 512 h42496 checked_43008
  have h43520 := checkBoolChunk_sound valid facts instructions 43520 512 h43008 checked_43520
  have h44032 := checkBoolChunk_sound valid facts instructions 44032 512 h43520 checked_44032
  have h44544 := checkBoolChunk_sound valid facts instructions 44544 512 h44032 checked_44544
  exact h44544

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
