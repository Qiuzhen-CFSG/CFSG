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
private theorem checked_118784 : checkBoolChunk context facts instructions 118784 77 = true := by decide +kernel

theorem advance_118784 {G : Type*} [Group G] {H : Subgroup G}
    {g : Nat → G} {ρ : Nat → G} (valid : Valid context H g ρ)
    (prior : ∀ n, n < 118784 → Holds H g ρ (facts n)) :
    ∀ n, n < 118861 → Holds H g ρ (facts n) := by
  have h118784 := checkBoolChunk_sound valid facts instructions 118784 77 prior checked_118784
  exact h118784

end Tits.AmalgamRigidity.FullRee.BadBraid.Case1
