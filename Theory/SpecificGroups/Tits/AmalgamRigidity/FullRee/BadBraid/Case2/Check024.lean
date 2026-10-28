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
private theorem checked_98304 : checkBoolChunk context facts instructions 98304 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_98816 : checkBoolChunk context facts instructions 98816 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_99328 : checkBoolChunk context facts instructions 99328 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_99840 : checkBoolChunk context facts instructions 99840 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_100352 : checkBoolChunk context facts instructions 100352 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_100864 : checkBoolChunk context facts instructions 100864 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_101376 : checkBoolChunk context facts instructions 101376 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_101888 : checkBoolChunk context facts instructions 101888 512 = true := by decide +kernel

theorem advance_98304 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 98304 → Holds H g ρ (facts n)) :
    ∀ n, n < 102400 → Holds H g ρ (facts n) := by
  have h98304 := checkBoolChunk_sound valid facts instructions 98304 512 prior checked_98304
  have h98816 := checkBoolChunk_sound valid facts instructions 98816 512 h98304 checked_98816
  have h99328 := checkBoolChunk_sound valid facts instructions 99328 512 h98816 checked_99328
  have h99840 := checkBoolChunk_sound valid facts instructions 99840 512 h99328 checked_99840
  have h100352 := checkBoolChunk_sound valid facts instructions 100352 512 h99840 checked_100352
  have h100864 := checkBoolChunk_sound valid facts instructions 100864 512 h100352 checked_100864
  have h101376 := checkBoolChunk_sound valid facts instructions 101376 512 h100864 checked_101376
  have h101888 := checkBoolChunk_sound valid facts instructions 101888 512 h101376 checked_101888
  exact h101888

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
