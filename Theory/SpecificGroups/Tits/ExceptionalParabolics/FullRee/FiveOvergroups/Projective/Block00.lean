module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Data

/-! First moderate block of projective max4 transfer checks. -/

public section
namespace Tits.Max4Projective
open Tits.MinimumIndexCandidates.OrderCertificate.Max4

theorem raw0Block0 : ∀ (i:Fin 4)(r:Fin 25),
    (raw0Gen i).mul (raw0Rep (⟨25*0+r.val,by omega⟩)) =
      (raw0Rep (L0Act i (⟨25*0+r.val,by omega⟩))).mul
        (evalRaw raw1Gen (L0Factor i (⟨25*0+r.val,by omega⟩))) ∨
    (raw0Gen i).mul (raw0Rep (⟨25*0+r.val,by omega⟩)) =
      ((raw0Rep (L0Act i (⟨25*0+r.val,by omega⟩))).mul
        (evalRaw raw1Gen (L0Factor i (⟨25*0+r.val,by omega⟩)))).neg := by decide +kernel
end Tits.Max4Projective
