module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 105–114

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp105 : CompositionCheck 101 := by
  change ∀ x : Fin 4060, m105 x.val = Part6Nat.force m60 (m56 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp106 : CompositionCheck 102 := by
  change ∀ x : Fin 4060, m106 x.val = Part6Nat.force m55 (m57 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp107 : CompositionCheck 103 := by
  change ∀ x : Fin 4060, m107 x.val = Part6Nat.force m0 (m25 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp108 : CompositionCheck 104 := by
  change ∀ x : Fin 4060, m108 x.val = Part6Nat.force m0 (m54 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp109 : CompositionCheck 105 := by
  change ∀ x : Fin 4060, m109 x.val = Part6Nat.force m58 (m25 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp110 : CompositionCheck 106 := by
  change ∀ x : Fin 4060, m110 x.val = Part6Nat.force m28 (m49 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp111 : CompositionCheck 107 := by
  change ∀ x : Fin 4060, m111 x.val = Part6Nat.force m6 (m25 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp112 : CompositionCheck 108 := by
  change ∀ x : Fin 4060, m112 x.val = Part6Nat.force m0 (m70 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp113 : CompositionCheck 109 := by
  change ∀ x : Fin 4060, m113 x.val = Part6Nat.force m91 (m24 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp114 : CompositionCheck 110 := by
  change ∀ x : Fin 4060, m114 x.val = Part6Nat.force m6 (m7 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
