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
private theorem checked_139264 : checkBoolChunk context facts instructions 139264 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_139776 : checkBoolChunk context facts instructions 139776 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_140288 : checkBoolChunk context facts instructions 140288 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_140800 : checkBoolChunk context facts instructions 140800 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_141312 : checkBoolChunk context facts instructions 141312 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_141824 : checkBoolChunk context facts instructions 141824 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_142336 : checkBoolChunk context facts instructions 142336 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_142848 : checkBoolChunk context facts instructions 142848 512 = true := by decide +kernel

theorem advance_139264 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 139264 → Holds H g ρ (facts n)) :
    ∀ n, n < 143360 → Holds H g ρ (facts n) := by
  have h139264 := checkBoolChunk_sound valid facts instructions 139264 512 prior checked_139264
  have h139776 := checkBoolChunk_sound valid facts instructions 139776 512 h139264 checked_139776
  have h140288 := checkBoolChunk_sound valid facts instructions 140288 512 h139776 checked_140288
  have h140800 := checkBoolChunk_sound valid facts instructions 140800 512 h140288 checked_140800
  have h141312 := checkBoolChunk_sound valid facts instructions 141312 512 h140800 checked_141312
  have h141824 := checkBoolChunk_sound valid facts instructions 141824 512 h141312 checked_141824
  have h142336 := checkBoolChunk_sound valid facts instructions 142336 512 h141824 checked_142336
  have h142848 := checkBoolChunk_sound valid facts instructions 142848 512 h142336 checked_142848
  exact h142848

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
