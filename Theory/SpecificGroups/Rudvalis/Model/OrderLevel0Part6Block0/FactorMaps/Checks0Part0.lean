module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 5–14

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp5 : CompositionCheck 1 := by
  change ∀ x : Fin 4060, m5 x.val = Part6Nat.force m3 (m0 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp6 : CompositionCheck 2 := by
  change ∀ x : Fin 4060, m6 x.val = Part6Nat.force m3 (m2 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp7 : CompositionCheck 3 := by
  change ∀ x : Fin 4060, m7 x.val = Part6Nat.force m1 (m0 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp8 : CompositionCheck 4 := by
  change ∀ x : Fin 4060, m8 x.val = Part6Nat.force m4 (m4 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp9 : CompositionCheck 5 := by
  change ∀ x : Fin 4060, m9 x.val = Part6Nat.force m6 (m8 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp10 : CompositionCheck 6 := by
  change ∀ x : Fin 4060, m10 x.val = Part6Nat.force m6 (m9 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp11 : CompositionCheck 7 := by
  change ∀ x : Fin 4060, m11 x.val = Part6Nat.force m5 (m7 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp12 : CompositionCheck 8 := by
  change ∀ x : Fin 4060, m12 x.val = Part6Nat.force m5 (m11 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp13 : CompositionCheck 9 := by
  change ∀ x : Fin 4060, m13 x.val = Part6Nat.force m10 (m2 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp14 : CompositionCheck 10 := by
  change ∀ x : Fin 4060, m14 x.val = Part6Nat.force m7 (m12 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
