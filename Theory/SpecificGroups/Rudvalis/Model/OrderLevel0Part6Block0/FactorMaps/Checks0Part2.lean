module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 25–34

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp25 : CompositionCheck 21 := by
  change ∀ x : Fin 4060, m25 x.val = Part6Nat.force m1 (m7 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp26 : CompositionCheck 22 := by
  change ∀ x : Fin 4060, m26 x.val = Part6Nat.force m5 (m21 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp27 : CompositionCheck 23 := by
  change ∀ x : Fin 4060, m27 x.val = Part6Nat.force m13 (m7 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp28 : CompositionCheck 24 := by
  change ∀ x : Fin 4060, m28 x.val = Part6Nat.force m19 (m20 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp29 : CompositionCheck 25 := by
  change ∀ x : Fin 4060, m29 x.val = Part6Nat.force m23 (m26 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp30 : CompositionCheck 26 := by
  change ∀ x : Fin 4060, m30 x.val = Part6Nat.force m25 (m29 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp31 : CompositionCheck 27 := by
  change ∀ x : Fin 4060, m31 x.val = Part6Nat.force m0 (m22 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp32 : CompositionCheck 28 := by
  change ∀ x : Fin 4060, m32 x.val = Part6Nat.force m19 (m30 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp33 : CompositionCheck 29 := by
  change ∀ x : Fin 4060, m33 x.val = Part6Nat.force m27 (m31 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp34 : CompositionCheck 30 := by
  change ∀ x : Fin 4060, m34 x.val = Part6Nat.force m24 (m10 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
