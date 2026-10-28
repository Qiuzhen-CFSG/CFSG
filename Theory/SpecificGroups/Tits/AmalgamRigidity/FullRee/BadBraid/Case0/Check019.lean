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
private theorem checked_77824 : checkBoolChunk context facts instructions 77824 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_78336 : checkBoolChunk context facts instructions 78336 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_78848 : checkBoolChunk context facts instructions 78848 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_79360 : checkBoolChunk context facts instructions 79360 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_79872 : checkBoolChunk context facts instructions 79872 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_80384 : checkBoolChunk context facts instructions 80384 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_80896 : checkBoolChunk context facts instructions 80896 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_81408 : checkBoolChunk context facts instructions 81408 512 = true := by decide +kernel

theorem advance_77824 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 77824 → Holds H g ρ (facts n)) :
    ∀ n, n < 81920 → Holds H g ρ (facts n) := by
  have h77824 := checkBoolChunk_sound valid facts instructions 77824 512 prior checked_77824
  have h78336 := checkBoolChunk_sound valid facts instructions 78336 512 h77824 checked_78336
  have h78848 := checkBoolChunk_sound valid facts instructions 78848 512 h78336 checked_78848
  have h79360 := checkBoolChunk_sound valid facts instructions 79360 512 h78848 checked_79360
  have h79872 := checkBoolChunk_sound valid facts instructions 79872 512 h79360 checked_79872
  have h80384 := checkBoolChunk_sound valid facts instructions 80384 512 h79872 checked_80384
  have h80896 := checkBoolChunk_sound valid facts instructions 80896 512 h80384 checked_80896
  have h81408 := checkBoolChunk_sound valid facts instructions 81408 512 h80896 checked_81408
  exact h81408

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
