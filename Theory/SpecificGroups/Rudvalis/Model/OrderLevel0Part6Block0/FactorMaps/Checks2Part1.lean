module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 75–84

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp75 : CompositionCheck 71 := by
  change ∀ x : Fin 4060, m75 x.val = Part6Nat.force m24 (m21 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp76 : CompositionCheck 72 := by
  change ∀ x : Fin 4060, m76 x.val = Part6Nat.force m32 (m67 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp77 : CompositionCheck 73 := by
  change ∀ x : Fin 4060, m77 x.val = Part6Nat.force m32 (m24 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp78 : CompositionCheck 74 := by
  change ∀ x : Fin 4060, m78 x.val = Part6Nat.force m77 (m3 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp79 : CompositionCheck 75 := by
  change ∀ x : Fin 4060, m79 x.val = Part6Nat.force m2 (m6 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp80 : CompositionCheck 76 := by
  change ∀ x : Fin 4060, m80 x.val = Part6Nat.force m2 (m5 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp81 : CompositionCheck 77 := by
  change ∀ x : Fin 4060, m81 x.val = Part6Nat.force m6 (m30 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp82 : CompositionCheck 78 := by
  change ∀ x : Fin 4060, m82 x.val = Part6Nat.force m17 (m59 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp83 : CompositionCheck 79 := by
  change ∀ x : Fin 4060, m83 x.val = Part6Nat.force m37 (m53 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp84 : CompositionCheck 80 := by
  change ∀ x : Fin 4060, m84 x.val = Part6Nat.force m65 (m22 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
