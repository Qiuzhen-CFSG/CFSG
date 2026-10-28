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
private theorem checked_69632 : checkBoolChunk context facts instructions 69632 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_70144 : checkBoolChunk context facts instructions 70144 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_70656 : checkBoolChunk context facts instructions 70656 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_71168 : checkBoolChunk context facts instructions 71168 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_71680 : checkBoolChunk context facts instructions 71680 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_72192 : checkBoolChunk context facts instructions 72192 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_72704 : checkBoolChunk context facts instructions 72704 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_73216 : checkBoolChunk context facts instructions 73216 512 = true := by decide +kernel

theorem advance_69632 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 69632 → Holds H g ρ (facts n)) :
    ∀ n, n < 73728 → Holds H g ρ (facts n) := by
  have h69632 := checkBoolChunk_sound valid facts instructions 69632 512 prior checked_69632
  have h70144 := checkBoolChunk_sound valid facts instructions 70144 512 h69632 checked_70144
  have h70656 := checkBoolChunk_sound valid facts instructions 70656 512 h70144 checked_70656
  have h71168 := checkBoolChunk_sound valid facts instructions 71168 512 h70656 checked_71168
  have h71680 := checkBoolChunk_sound valid facts instructions 71680 512 h71168 checked_71680
  have h72192 := checkBoolChunk_sound valid facts instructions 72192 512 h71680 checked_72192
  have h72704 := checkBoolChunk_sound valid facts instructions 72704 512 h72192 checked_72704
  have h73216 := checkBoolChunk_sound valid facts instructions 73216 512 h72704 checked_73216
  exact h73216

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
