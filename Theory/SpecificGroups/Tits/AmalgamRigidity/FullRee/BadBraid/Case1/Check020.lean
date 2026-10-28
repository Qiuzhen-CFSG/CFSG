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
private theorem checked_81920 : checkBoolChunk context facts instructions 81920 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_82432 : checkBoolChunk context facts instructions 82432 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_82944 : checkBoolChunk context facts instructions 82944 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_83456 : checkBoolChunk context facts instructions 83456 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_83968 : checkBoolChunk context facts instructions 83968 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_84480 : checkBoolChunk context facts instructions 84480 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_84992 : checkBoolChunk context facts instructions 84992 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_85504 : checkBoolChunk context facts instructions 85504 512 = true := by decide +kernel

theorem advance_81920 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 81920 → Holds H g ρ (facts n)) :
    ∀ n, n < 86016 → Holds H g ρ (facts n) := by
  have h81920 := checkBoolChunk_sound valid facts instructions 81920 512 prior checked_81920
  have h82432 := checkBoolChunk_sound valid facts instructions 82432 512 h81920 checked_82432
  have h82944 := checkBoolChunk_sound valid facts instructions 82944 512 h82432 checked_82944
  have h83456 := checkBoolChunk_sound valid facts instructions 83456 512 h82944 checked_83456
  have h83968 := checkBoolChunk_sound valid facts instructions 83968 512 h83456 checked_83968
  have h84480 := checkBoolChunk_sound valid facts instructions 84480 512 h83968 checked_84480
  have h84992 := checkBoolChunk_sound valid facts instructions 84992 512 h84480 checked_84992
  have h85504 := checkBoolChunk_sound valid facts instructions 85504 512 h84992 checked_85504
  exact h85504

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
