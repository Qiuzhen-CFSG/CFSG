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
private theorem checked_159744 : checkBoolChunk context facts instructions 159744 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_160256 : checkBoolChunk context facts instructions 160256 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_160768 : checkBoolChunk context facts instructions 160768 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_161280 : checkBoolChunk context facts instructions 161280 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_161792 : checkBoolChunk context facts instructions 161792 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_162304 : checkBoolChunk context facts instructions 162304 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_162816 : checkBoolChunk context facts instructions 162816 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_163328 : checkBoolChunk context facts instructions 163328 512 = true := by decide +kernel

theorem advance_159744 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 159744 → Holds H g ρ (facts n)) :
    ∀ n, n < 163840 → Holds H g ρ (facts n) := by
  have h159744 := checkBoolChunk_sound valid facts instructions 159744 512 prior checked_159744
  have h160256 := checkBoolChunk_sound valid facts instructions 160256 512 h159744 checked_160256
  have h160768 := checkBoolChunk_sound valid facts instructions 160768 512 h160256 checked_160768
  have h161280 := checkBoolChunk_sound valid facts instructions 161280 512 h160768 checked_161280
  have h161792 := checkBoolChunk_sound valid facts instructions 161792 512 h161280 checked_161792
  have h162304 := checkBoolChunk_sound valid facts instructions 162304 512 h161792 checked_162304
  have h162816 := checkBoolChunk_sound valid facts instructions 162816 512 h162304 checked_162816
  have h163328 := checkBoolChunk_sound valid facts instructions 163328 512 h162816 checked_163328
  exact h163328

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
