module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 35–44

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp35 : CompositionCheck 31 := by
  change ∀ x : Fin 4060, m35 x.val = Part6Nat.force m6 (m20 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp36 : CompositionCheck 32 := by
  change ∀ x : Fin 4060, m36 x.val = Part6Nat.force m1 (m18 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp37 : CompositionCheck 33 := by
  change ∀ x : Fin 4060, m37 x.val = Part6Nat.force m32 (m34 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp38 : CompositionCheck 34 := by
  change ∀ x : Fin 4060, m38 x.val = Part6Nat.force m37 (m33 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp39 : CompositionCheck 35 := by
  change ∀ x : Fin 4060, m39 x.val = Part6Nat.force m18 (m28 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp40 : CompositionCheck 36 := by
  change ∀ x : Fin 4060, m40 x.val = Part6Nat.force m18 (m17 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp41 : CompositionCheck 37 := by
  change ∀ x : Fin 4060, m41 x.val = Part6Nat.force m4 (m9 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp42 : CompositionCheck 38 := by
  change ∀ x : Fin 4060, m42 x.val = Part6Nat.force m8 (m38 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp43 : CompositionCheck 39 := by
  change ∀ x : Fin 4060, m43 x.val = Part6Nat.force m39 (m36 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp44 : CompositionCheck 40 := by
  change ∀ x : Fin 4060, m44 x.val = Part6Nat.force m40 (m43 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
