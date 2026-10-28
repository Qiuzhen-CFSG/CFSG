module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Data

/-! Moderate block 1 of projective max4 transfer checks. -/

public section
namespace Tits.Max4Projective
open Tits.MinimumIndexCandidates.OrderCertificate.Max4

theorem raw0Block1 : ∀ (i:Fin 4)(r:Fin 25),
    (raw0Gen i).mul (raw0Rep (⟨25*1+r.val,by omega⟩)) =
      (raw0Rep (L0Act i (⟨25*1+r.val,by omega⟩))).mul
        (evalRaw raw1Gen (L0Factor i (⟨25*1+r.val,by omega⟩))) ∨
    (raw0Gen i).mul (raw0Rep (⟨25*1+r.val,by omega⟩)) =
      ((raw0Rep (L0Act i (⟨25*1+r.val,by omega⟩))).mul
        (evalRaw raw1Gen (L0Factor i (⟨25*1+r.val,by omega⟩)))).neg := by decide +kernel
end Tits.Max4Projective
