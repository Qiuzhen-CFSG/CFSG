module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 15–24

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp15 : CompositionCheck 11 := by
  change ∀ x : Fin 4060, m15 x.val = Part6Nat.force m5 (m0 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp16 : CompositionCheck 12 := by
  change ∀ x : Fin 4060, m16 x.val = Part6Nat.force m5 (m3 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp17 : CompositionCheck 13 := by
  change ∀ x : Fin 4060, m17 x.val = Part6Nat.force m15 (m12 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp18 : CompositionCheck 14 := by
  change ∀ x : Fin 4060, m18 x.val = Part6Nat.force m4 (m7 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp19 : CompositionCheck 15 := by
  change ∀ x : Fin 4060, m19 x.val = Part6Nat.force m16 (m6 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp20 : CompositionCheck 16 := by
  change ∀ x : Fin 4060, m20 x.val = Part6Nat.force m3 (m5 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp21 : CompositionCheck 17 := by
  change ∀ x : Fin 4060, m21 x.val = Part6Nat.force m13 (m4 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp22 : CompositionCheck 18 := by
  change ∀ x : Fin 4060, m22 x.val = Part6Nat.force m17 (m14 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp23 : CompositionCheck 19 := by
  change ∀ x : Fin 4060, m23 x.val = Part6Nat.force m1 (m8 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp24 : CompositionCheck 20 := by
  change ∀ x : Fin 4060, m24 x.val = Part6Nat.force m5 (m10 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
