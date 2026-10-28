module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 55–64

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp55 : CompositionCheck 51 := by
  change ∀ x : Fin 4060, m55 x.val = Part6Nat.force m28 (m41 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp56 : CompositionCheck 52 := by
  change ∀ x : Fin 4060, m56 x.val = Part6Nat.force m2 (m7 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp57 : CompositionCheck 53 := by
  change ∀ x : Fin 4060, m57 x.val = Part6Nat.force m2 (m4 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp58 : CompositionCheck 54 := by
  change ∀ x : Fin 4060, m58 x.val = Part6Nat.force m0 (m5 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp59 : CompositionCheck 55 := by
  change ∀ x : Fin 4060, m59 x.val = Part6Nat.force m35 (m23 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp60 : CompositionCheck 56 := by
  change ∀ x : Fin 4060, m60 x.val = Part6Nat.force m35 (m41 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp61 : CompositionCheck 57 := by
  change ∀ x : Fin 4060, m61 x.val = Part6Nat.force m21 (m52 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp62 : CompositionCheck 58 := by
  change ∀ x : Fin 4060, m62 x.val = Part6Nat.force m48 (m36 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp63 : CompositionCheck 59 := by
  change ∀ x : Fin 4060, m63 x.val = Part6Nat.force m28 (m23 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp64 : CompositionCheck 60 := by
  change ∀ x : Fin 4060, m64 x.val = Part6Nat.force m18 (m0 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
