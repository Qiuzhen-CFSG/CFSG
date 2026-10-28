module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 45–54

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp45 : CompositionCheck 41 := by
  change ∀ x : Fin 4060, m45 x.val = Part6Nat.force m14 (m44 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp46 : CompositionCheck 42 := by
  change ∀ x : Fin 4060, m46 x.val = Part6Nat.force m45 (m16 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp47 : CompositionCheck 43 := by
  change ∀ x : Fin 4060, m47 x.val = Part6Nat.force m22 (m46 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp48 : CompositionCheck 44 := by
  change ∀ x : Fin 4060, m48 x.val = Part6Nat.force m3 (m35 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp49 : CompositionCheck 45 := by
  change ∀ x : Fin 4060, m49 x.val = Part6Nat.force m1 (m14 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp50 : CompositionCheck 46 := by
  change ∀ x : Fin 4060, m50 x.val = Part6Nat.force m0 (m7 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp51 : CompositionCheck 47 := by
  change ∀ x : Fin 4060, m51 x.val = Part6Nat.force m21 (m2 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp52 : CompositionCheck 48 := by
  change ∀ x : Fin 4060, m52 x.val = Part6Nat.force m22 (m42 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp53 : CompositionCheck 49 := by
  change ∀ x : Fin 4060, m53 x.val = Part6Nat.force m51 (m47 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp54 : CompositionCheck 50 := by
  change ∀ x : Fin 4060, m54 x.val = Part6Nat.force m1 (m4 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
