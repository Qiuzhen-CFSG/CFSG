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
private theorem checked_167936 : checkBoolChunk context facts instructions 167936 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_168448 : checkBoolChunk context facts instructions 168448 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_168960 : checkBoolChunk context facts instructions 168960 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_169472 : checkBoolChunk context facts instructions 169472 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_169984 : checkBoolChunk context facts instructions 169984 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_170496 : checkBoolChunk context facts instructions 170496 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_171008 : checkBoolChunk context facts instructions 171008 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_171520 : checkBoolChunk context facts instructions 171520 512 = true := by decide +kernel

theorem advance_167936 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 167936 → Holds H g ρ (facts n)) :
    ∀ n, n < 172032 → Holds H g ρ (facts n) := by
  have h167936 := checkBoolChunk_sound valid facts instructions 167936 512 prior checked_167936
  have h168448 := checkBoolChunk_sound valid facts instructions 168448 512 h167936 checked_168448
  have h168960 := checkBoolChunk_sound valid facts instructions 168960 512 h168448 checked_168960
  have h169472 := checkBoolChunk_sound valid facts instructions 169472 512 h168960 checked_169472
  have h169984 := checkBoolChunk_sound valid facts instructions 169984 512 h169472 checked_169984
  have h170496 := checkBoolChunk_sound valid facts instructions 170496 512 h169984 checked_170496
  have h171008 := checkBoolChunk_sound valid facts instructions 171008 512 h170496 checked_171008
  have h171520 := checkBoolChunk_sound valid facts instructions 171520 512 h171008 checked_171520
  exact h171520

end Tits.AmalgamRigidity.FullRee.BadBraid.Case0
