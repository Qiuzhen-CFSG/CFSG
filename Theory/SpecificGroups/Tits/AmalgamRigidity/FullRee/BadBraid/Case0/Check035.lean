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
private theorem checked_143360 : checkBoolChunk context facts instructions 143360 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_143872 : checkBoolChunk context facts instructions 143872 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_144384 : checkBoolChunk context facts instructions 144384 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_144896 : checkBoolChunk context facts instructions 144896 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_145408 : checkBoolChunk context facts instructions 145408 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_145920 : checkBoolChunk context facts instructions 145920 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_146432 : checkBoolChunk context facts instructions 146432 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_146944 : checkBoolChunk context facts instructions 146944 512 = true := by decide +kernel

theorem advance_143360 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 143360 → Holds H g ρ (facts n)) :
    ∀ n, n < 147456 → Holds H g ρ (facts n) := by
  have h143360 := checkBoolChunk_sound valid facts instructions 143360 512 prior checked_143360
  have h143872 := checkBoolChunk_sound valid facts instructions 143872 512 h143360 checked_143872
  have h144384 := checkBoolChunk_sound valid facts instructions 144384 512 h143872 checked_144384
  have h144896 := checkBoolChunk_sound valid facts instructions 144896 512 h144384 checked_144896
  have h145408 := checkBoolChunk_sound valid facts instructions 145408 512 h144896 checked_145408
  have h145920 := checkBoolChunk_sound valid facts instructions 145920 512 h145408 checked_145920
  have h146432 := checkBoolChunk_sound valid facts instructions 146432 512 h145920 checked_146432
  have h146944 := checkBoolChunk_sound valid facts instructions 146944 512 h146432 checked_146944
  exact h146944

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
