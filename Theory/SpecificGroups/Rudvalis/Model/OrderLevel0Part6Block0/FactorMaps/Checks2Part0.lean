module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 65–74

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp65 : CompositionCheck 61 := by
  change ∀ x : Fin 4060, m65 x.val = Part6Nat.force m24 (m27 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp66 : CompositionCheck 62 := by
  change ∀ x : Fin 4060, m66 x.val = Part6Nat.force m35 (m49 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp67 : CompositionCheck 63 := by
  change ∀ x : Fin 4060, m67 x.val = Part6Nat.force m26 (m38 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp68 : CompositionCheck 64 := by
  change ∀ x : Fin 4060, m68 x.val = Part6Nat.force m24 (m53 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp69 : CompositionCheck 65 := by
  change ∀ x : Fin 4060, m69 x.val = Part6Nat.force m48 (m41 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp70 : CompositionCheck 66 := by
  change ∀ x : Fin 4060, m70 x.val = Part6Nat.force m0 (m6 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp71 : CompositionCheck 67 := by
  change ∀ x : Fin 4060, m71 x.val = Part6Nat.force m28 (m36 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp72 : CompositionCheck 68 := by
  change ∀ x : Fin 4060, m72 x.val = Part6Nat.force m33 (m42 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp73 : CompositionCheck 69 := by
  change ∀ x : Fin 4060, m73 x.val = Part6Nat.force m61 (m42 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp74 : CompositionCheck 70 := by
  change ∀ x : Fin 4060, m74 x.val = Part6Nat.force m14 (m14 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
