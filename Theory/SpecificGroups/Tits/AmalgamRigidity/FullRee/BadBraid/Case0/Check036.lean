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
private theorem checked_147456 : checkBoolChunk context facts instructions 147456 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_147968 : checkBoolChunk context facts instructions 147968 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_148480 : checkBoolChunk context facts instructions 148480 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_148992 : checkBoolChunk context facts instructions 148992 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_149504 : checkBoolChunk context facts instructions 149504 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_150016 : checkBoolChunk context facts instructions 150016 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_150528 : checkBoolChunk context facts instructions 150528 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_151040 : checkBoolChunk context facts instructions 151040 512 = true := by decide +kernel

theorem advance_147456 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 147456 → Holds H g ρ (facts n)) :
    ∀ n, n < 151552 → Holds H g ρ (facts n) := by
  have h147456 := checkBoolChunk_sound valid facts instructions 147456 512 prior checked_147456
  have h147968 := checkBoolChunk_sound valid facts instructions 147968 512 h147456 checked_147968
  have h148480 := checkBoolChunk_sound valid facts instructions 148480 512 h147968 checked_148480
  have h148992 := checkBoolChunk_sound valid facts instructions 148992 512 h148480 checked_148992
  have h149504 := checkBoolChunk_sound valid facts instructions 149504 512 h148992 checked_149504
  have h150016 := checkBoolChunk_sound valid facts instructions 150016 512 h149504 checked_150016
  have h150528 := checkBoolChunk_sound valid facts instructions 150528 512 h150016 checked_150528
  have h151040 := checkBoolChunk_sound valid facts instructions 151040 512 h150528 checked_151040
  exact h151040

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
