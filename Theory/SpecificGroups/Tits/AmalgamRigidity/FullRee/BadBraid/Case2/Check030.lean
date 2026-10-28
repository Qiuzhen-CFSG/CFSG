module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Context
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.Case2.Data

/-! Kernel replay for a nonstandard binary Ree reflection pair.
Generated from the six sound coset-word rules; see `../source/README.md`. -/

public section
namespace Tits.AmalgamRigidity.FullRee.BadBraid.Case2
open Subgroup.CosetWordCertificate
set_option Elab.async false

set_option maxRecDepth 4096 in
private theorem checked_122880 : checkBoolChunk context facts instructions 122880 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_123392 : checkBoolChunk context facts instructions 123392 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_123904 : checkBoolChunk context facts instructions 123904 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_124416 : checkBoolChunk context facts instructions 124416 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_124928 : checkBoolChunk context facts instructions 124928 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_125440 : checkBoolChunk context facts instructions 125440 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_125952 : checkBoolChunk context facts instructions 125952 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_126464 : checkBoolChunk context facts instructions 126464 512 = true := by decide +kernel

theorem advance_122880 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 122880 → Holds H g ρ (facts n)) :
    ∀ n, n < 126976 → Holds H g ρ (facts n) := by
  have h122880 := checkBoolChunk_sound valid facts instructions 122880 512 prior checked_122880
  have h123392 := checkBoolChunk_sound valid facts instructions 123392 512 h122880 checked_123392
  have h123904 := checkBoolChunk_sound valid facts instructions 123904 512 h123392 checked_123904
  have h124416 := checkBoolChunk_sound valid facts instructions 124416 512 h123904 checked_124416
  have h124928 := checkBoolChunk_sound valid facts instructions 124928 512 h124416 checked_124928
  have h125440 := checkBoolChunk_sound valid facts instructions 125440 512 h124928 checked_125440
  have h125952 := checkBoolChunk_sound valid facts instructions 125952 512 h125440 checked_125952
  have h126464 := checkBoolChunk_sound valid facts instructions 126464 512 h125952 checked_126464
  exact h126464

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
