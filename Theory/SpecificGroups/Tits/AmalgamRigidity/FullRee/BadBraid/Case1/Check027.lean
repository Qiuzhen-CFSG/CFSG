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
private theorem checked_110592 : checkBoolChunk context facts instructions 110592 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_111104 : checkBoolChunk context facts instructions 111104 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_111616 : checkBoolChunk context facts instructions 111616 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_112128 : checkBoolChunk context facts instructions 112128 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_112640 : checkBoolChunk context facts instructions 112640 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_113152 : checkBoolChunk context facts instructions 113152 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_113664 : checkBoolChunk context facts instructions 113664 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_114176 : checkBoolChunk context facts instructions 114176 512 = true := by decide +kernel

theorem advance_110592 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 110592 → Holds H g ρ (facts n)) :
    ∀ n, n < 114688 → Holds H g ρ (facts n) := by
  have h110592 := checkBoolChunk_sound valid facts instructions 110592 512 prior checked_110592
  have h111104 := checkBoolChunk_sound valid facts instructions 111104 512 h110592 checked_111104
  have h111616 := checkBoolChunk_sound valid facts instructions 111616 512 h111104 checked_111616
  have h112128 := checkBoolChunk_sound valid facts instructions 112128 512 h111616 checked_112128
  have h112640 := checkBoolChunk_sound valid facts instructions 112640 512 h112128 checked_112640
  have h113152 := checkBoolChunk_sound valid facts instructions 113152 512 h112640 checked_113152
  have h113664 := checkBoolChunk_sound valid facts instructions 113664 512 h113152 checked_113664
  have h114176 := checkBoolChunk_sound valid facts instructions 114176 512 h113664 checked_114176
  exact h114176

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
