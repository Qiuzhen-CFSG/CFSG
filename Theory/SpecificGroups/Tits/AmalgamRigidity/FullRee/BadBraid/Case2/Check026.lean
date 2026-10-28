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
private theorem checked_106496 : checkBoolChunk context facts instructions 106496 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_107008 : checkBoolChunk context facts instructions 107008 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_107520 : checkBoolChunk context facts instructions 107520 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_108032 : checkBoolChunk context facts instructions 108032 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_108544 : checkBoolChunk context facts instructions 108544 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_109056 : checkBoolChunk context facts instructions 109056 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_109568 : checkBoolChunk context facts instructions 109568 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_110080 : checkBoolChunk context facts instructions 110080 512 = true := by decide +kernel

theorem advance_106496 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 106496 → Holds H g ρ (facts n)) :
    ∀ n, n < 110592 → Holds H g ρ (facts n) := by
  have h106496 := checkBoolChunk_sound valid facts instructions 106496 512 prior checked_106496
  have h107008 := checkBoolChunk_sound valid facts instructions 107008 512 h106496 checked_107008
  have h107520 := checkBoolChunk_sound valid facts instructions 107520 512 h107008 checked_107520
  have h108032 := checkBoolChunk_sound valid facts instructions 108032 512 h107520 checked_108032
  have h108544 := checkBoolChunk_sound valid facts instructions 108544 512 h108032 checked_108544
  have h109056 := checkBoolChunk_sound valid facts instructions 109056 512 h108544 checked_109056
  have h109568 := checkBoolChunk_sound valid facts instructions 109568 512 h109056 checked_109568
  have h110080 := checkBoolChunk_sound valid facts instructions 110080 512 h109568 checked_110080
  exact h110080

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
