module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 115–124

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp115 : CompositionCheck 111 := by
  change ∀ x : Fin 4060, m115 x.val = Part6Nat.force m28 (m1 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp116 : CompositionCheck 112 := by
  change ∀ x : Fin 4060, m116 x.val = Part6Nat.force m0 (m50 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp117 : CompositionCheck 113 := by
  change ∀ x : Fin 4060, m117 x.val = Part6Nat.force m9 (m57 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp118 : CompositionCheck 114 := by
  change ∀ x : Fin 4060, m118 x.val = Part6Nat.force m50 (m0 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp119 : CompositionCheck 115 := by
  change ∀ x : Fin 4060, m119 x.val = Part6Nat.force m0 (m34 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp120 : CompositionCheck 116 := by
  change ∀ x : Fin 4060, m120 x.val = Part6Nat.force m11 (m12 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp121 : CompositionCheck 117 := by
  change ∀ x : Fin 4060, m121 x.val = Part6Nat.force m17 (m8 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp122 : CompositionCheck 118 := by
  change ∀ x : Fin 4060, m122 x.val = Part6Nat.force m39 (m23 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp123 : CompositionCheck 119 := by
  change ∀ x : Fin 4060, m123 x.val = Part6Nat.force m122 (m63 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp124 : CompositionCheck 120 := by
  change ∀ x : Fin 4060, m124 x.val = Part6Nat.force m123 (m78 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
