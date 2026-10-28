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
private theorem checked_172032 : checkBoolChunk context facts instructions 172032 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_172544 : checkBoolChunk context facts instructions 172544 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_173056 : checkBoolChunk context facts instructions 173056 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_173568 : checkBoolChunk context facts instructions 173568 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_174080 : checkBoolChunk context facts instructions 174080 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_174592 : checkBoolChunk context facts instructions 174592 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_175104 : checkBoolChunk context facts instructions 175104 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_175616 : checkBoolChunk context facts instructions 175616 512 = true := by decide +kernel

theorem advance_172032 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 172032 → Holds H g ρ (facts n)) :
    ∀ n, n < 176128 → Holds H g ρ (facts n) := by
  have h172032 := checkBoolChunk_sound valid facts instructions 172032 512 prior checked_172032
  have h172544 := checkBoolChunk_sound valid facts instructions 172544 512 h172032 checked_172544
  have h173056 := checkBoolChunk_sound valid facts instructions 173056 512 h172544 checked_173056
  have h173568 := checkBoolChunk_sound valid facts instructions 173568 512 h173056 checked_173568
  have h174080 := checkBoolChunk_sound valid facts instructions 174080 512 h173568 checked_174080
  have h174592 := checkBoolChunk_sound valid facts instructions 174592 512 h174080 checked_174592
  have h175104 := checkBoolChunk_sound valid facts instructions 175104 512 h174592 checked_175104
  have h175616 := checkBoolChunk_sound valid facts instructions 175616 512 h175104 checked_175616
  exact h175616

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
