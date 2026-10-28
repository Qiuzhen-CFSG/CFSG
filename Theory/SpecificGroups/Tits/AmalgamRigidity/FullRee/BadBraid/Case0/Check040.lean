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
private theorem checked_163840 : checkBoolChunk context facts instructions 163840 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_164352 : checkBoolChunk context facts instructions 164352 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_164864 : checkBoolChunk context facts instructions 164864 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_165376 : checkBoolChunk context facts instructions 165376 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_165888 : checkBoolChunk context facts instructions 165888 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_166400 : checkBoolChunk context facts instructions 166400 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_166912 : checkBoolChunk context facts instructions 166912 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_167424 : checkBoolChunk context facts instructions 167424 512 = true := by decide +kernel

theorem advance_163840 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 163840 → Holds H g ρ (facts n)) :
    ∀ n, n < 167936 → Holds H g ρ (facts n) := by
  have h163840 := checkBoolChunk_sound valid facts instructions 163840 512 prior checked_163840
  have h164352 := checkBoolChunk_sound valid facts instructions 164352 512 h163840 checked_164352
  have h164864 := checkBoolChunk_sound valid facts instructions 164864 512 h164352 checked_164864
  have h165376 := checkBoolChunk_sound valid facts instructions 165376 512 h164864 checked_165376
  have h165888 := checkBoolChunk_sound valid facts instructions 165888 512 h165376 checked_165888
  have h166400 := checkBoolChunk_sound valid facts instructions 166400 512 h165888 checked_166400
  have h166912 := checkBoolChunk_sound valid facts instructions 166912 512 h166400 checked_166912
  have h167424 := checkBoolChunk_sound valid facts instructions 167424 512 h166912 checked_167424
  exact h167424

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
