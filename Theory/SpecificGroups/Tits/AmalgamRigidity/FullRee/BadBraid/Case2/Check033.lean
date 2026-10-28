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
private theorem checked_135168 : checkBoolChunk context facts instructions 135168 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_135680 : checkBoolChunk context facts instructions 135680 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_136192 : checkBoolChunk context facts instructions 136192 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_136704 : checkBoolChunk context facts instructions 136704 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_137216 : checkBoolChunk context facts instructions 137216 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_137728 : checkBoolChunk context facts instructions 137728 512 = true := by decide +kernel

set_option maxRecDepth 4096 in
private theorem checked_138240 : checkBoolChunk context facts instructions 138240 155 = true := by decide +kernel

theorem advance_135168 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 135168 → Holds H g ρ (facts n)) :
    ∀ n, n < 138395 → Holds H g ρ (facts n) := by
  have h135168 := checkBoolChunk_sound valid facts instructions 135168 512 prior checked_135168
  have h135680 := checkBoolChunk_sound valid facts instructions 135680 512 h135168 checked_135680
  have h136192 := checkBoolChunk_sound valid facts instructions 136192 512 h135680 checked_136192
  have h136704 := checkBoolChunk_sound valid facts instructions 136704 512 h136192 checked_136704
  have h137216 := checkBoolChunk_sound valid facts instructions 137216 512 h136704 checked_137216
  have h137728 := checkBoolChunk_sound valid facts instructions 137728 512 h137216 checked_137728
  have h138240 := checkBoolChunk_sound valid facts instructions 138240 155 h137728 checked_138240
  exact h138240

end Tits.AmalgamRigidity.FullRee.BadBraid.Case2
