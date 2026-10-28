module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 85–94

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp85 : CompositionCheck 81 := by
  change ∀ x : Fin 4060, m85 x.val = Part6Nat.force m35 (m36 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp86 : CompositionCheck 82 := by
  change ∀ x : Fin 4060, m86 x.val = Part6Nat.force m4 (m5 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp87 : CompositionCheck 83 := by
  change ∀ x : Fin 4060, m87 x.val = Part6Nat.force m49 (m14 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp88 : CompositionCheck 84 := by
  change ∀ x : Fin 4060, m88 x.val = Part6Nat.force m0 (m4 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp89 : CompositionCheck 85 := by
  change ∀ x : Fin 4060, m89 x.val = Part6Nat.force m5 (m6 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp90 : CompositionCheck 86 := by
  change ∀ x : Fin 4060, m90 x.val = Part6Nat.force m7 (m8 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp91 : CompositionCheck 87 := by
  change ∀ x : Fin 4060, m91 x.val = Part6Nat.force m5 (m27 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp92 : CompositionCheck 88 := by
  change ∀ x : Fin 4060, m92 x.val = Part6Nat.force m48 (m23 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp93 : CompositionCheck 89 := by
  change ∀ x : Fin 4060, m93 x.val = Part6Nat.force m64 (m17 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp94 : CompositionCheck 90 := by
  change ∀ x : Fin 4060, m94 x.val = Part6Nat.force m75 (m47 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
