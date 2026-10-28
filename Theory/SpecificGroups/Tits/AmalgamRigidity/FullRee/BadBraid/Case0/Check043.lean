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
private theorem checked_176128 : checkBoolChunk context facts instructions 176128 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_176640 : checkBoolChunk context facts instructions 176640 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_177152 : checkBoolChunk context facts instructions 177152 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_177664 : checkBoolChunk context facts instructions 177664 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_178176 : checkBoolChunk context facts instructions 178176 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_178688 : checkBoolChunk context facts instructions 178688 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_179200 : checkBoolChunk context facts instructions 179200 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_179712 : checkBoolChunk context facts instructions 179712 512 = true := by decide +kernel

theorem advance_176128 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 176128 → Holds H g ρ (facts n)) :
    ∀ n, n < 180224 → Holds H g ρ (facts n) := by
  have h176128 := checkBoolChunk_sound valid facts instructions 176128 512 prior checked_176128
  have h176640 := checkBoolChunk_sound valid facts instructions 176640 512 h176128 checked_176640
  have h177152 := checkBoolChunk_sound valid facts instructions 177152 512 h176640 checked_177152
  have h177664 := checkBoolChunk_sound valid facts instructions 177664 512 h177152 checked_177664
  have h178176 := checkBoolChunk_sound valid facts instructions 178176 512 h177664 checked_178176
  have h178688 := checkBoolChunk_sound valid facts instructions 178688 512 h178176 checked_178688
  have h179200 := checkBoolChunk_sound valid facts instructions 179200 512 h178688 checked_179200
  have h179712 := checkBoolChunk_sound valid facts instructions 179712 512 h179200 checked_179712
  exact h179712

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
