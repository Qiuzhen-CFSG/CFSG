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
private theorem checked_90112 : checkBoolChunk context facts instructions 90112 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_90624 : checkBoolChunk context facts instructions 90624 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_91136 : checkBoolChunk context facts instructions 91136 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_91648 : checkBoolChunk context facts instructions 91648 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_92160 : checkBoolChunk context facts instructions 92160 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_92672 : checkBoolChunk context facts instructions 92672 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_93184 : checkBoolChunk context facts instructions 93184 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_93696 : checkBoolChunk context facts instructions 93696 512 = true := by decide +kernel

theorem advance_90112 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 90112 → Holds H g ρ (facts n)) :
    ∀ n, n < 94208 → Holds H g ρ (facts n) := by
  have h90112 := checkBoolChunk_sound valid facts instructions 90112 512 prior checked_90112
  have h90624 := checkBoolChunk_sound valid facts instructions 90624 512 h90112 checked_90624
  have h91136 := checkBoolChunk_sound valid facts instructions 91136 512 h90624 checked_91136
  have h91648 := checkBoolChunk_sound valid facts instructions 91648 512 h91136 checked_91648
  have h92160 := checkBoolChunk_sound valid facts instructions 92160 512 h91648 checked_92160
  have h92672 := checkBoolChunk_sound valid facts instructions 92672 512 h92160 checked_92672
  have h93184 := checkBoolChunk_sound valid facts instructions 93184 512 h92672 checked_93184
  have h93696 := checkBoolChunk_sound valid facts instructions 93696 512 h93184 checked_93696
  exact h93696

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
