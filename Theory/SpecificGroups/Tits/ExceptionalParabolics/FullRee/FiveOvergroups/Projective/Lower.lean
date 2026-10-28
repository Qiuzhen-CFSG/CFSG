module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Projective.Data

/-! The two lower Schreier levels, checked in the same matrix model. -/

public section
namespace Tits.Max4Projective
open Tits.MinimumIndexCandidates.OrderCertificate.Max4
theorem raw1Step : ∀ (i:Fin 4)(r:Fin 13),
    (raw1Gen i).mul (raw1Rep r) =
      (raw1Rep (L1Act i r)).mul (evalRaw raw2Gen (L1Factor i r)) ∨
    (raw1Gen i).mul (raw1Rep r) =
      ((raw1Rep (L1Act i r)).mul (evalRaw raw2Gen (L1Factor i r))).neg := by decide +kernel
theorem raw2Step : ∀ (i:Fin 2)(r:Fin 2),
    (raw2Gen i).mul (raw2Rep r) =
      (raw2Rep (L2Act i r)).mul (evalRaw raw3Gen (L2Factor i r)) ∨
    (raw2Gen i).mul (raw2Rep r) =
      ((raw2Rep (L2Act i r)).mul (evalRaw raw3Gen (L2Factor i r))).neg := by decide +kernel
end Tits.Max4Projective
