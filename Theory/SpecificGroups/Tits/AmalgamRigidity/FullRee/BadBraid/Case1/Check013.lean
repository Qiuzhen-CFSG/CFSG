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
private theorem checked_53248 : checkBoolChunk context facts instructions 53248 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_53760 : checkBoolChunk context facts instructions 53760 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_54272 : checkBoolChunk context facts instructions 54272 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_54784 : checkBoolChunk context facts instructions 54784 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_55296 : checkBoolChunk context facts instructions 55296 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_55808 : checkBoolChunk context facts instructions 55808 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_56320 : checkBoolChunk context facts instructions 56320 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_56832 : checkBoolChunk context facts instructions 56832 512 = true := by decide +kernel

theorem advance_53248 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 53248 → Holds H g ρ (facts n)) :
    ∀ n, n < 57344 → Holds H g ρ (facts n) := by
  have h53248 := checkBoolChunk_sound valid facts instructions 53248 512 prior checked_53248
  have h53760 := checkBoolChunk_sound valid facts instructions 53760 512 h53248 checked_53760
  have h54272 := checkBoolChunk_sound valid facts instructions 54272 512 h53760 checked_54272
  have h54784 := checkBoolChunk_sound valid facts instructions 54784 512 h54272 checked_54784
  have h55296 := checkBoolChunk_sound valid facts instructions 55296 512 h54784 checked_55296
  have h55808 := checkBoolChunk_sound valid facts instructions 55808 512 h55296 checked_55808
  have h56320 := checkBoolChunk_sound valid facts instructions 56320 512 h55808 checked_56320
  have h56832 := checkBoolChunk_sound valid facts instructions 56832 512 h56320 checked_56832
  exact h56832

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
