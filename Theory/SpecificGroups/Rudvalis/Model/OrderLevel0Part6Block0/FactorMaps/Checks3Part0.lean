module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block0.FactorMaps.Data

/-!
# Binary factor-cache certificates 95–104

Each proposed map is checked on all 4060 points against its two parent maps.
Source: the ATLAS witnesses recorded in `Data` and `source/README.md`.
These checks require no other composition certificates.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
set_option Elab.async false
set_option maxRecDepth 30000

set_option maxHeartbeats 1600000 in
public theorem comp95 : CompositionCheck 91 := by
  change ∀ x : Fin 4060, m95 x.val = Part6Nat.force m39 (m41 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp96 : CompositionCheck 92 := by
  change ∀ x : Fin 4060, m96 x.val = Part6Nat.force m50 (m8 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp97 : CompositionCheck 93 := by
  change ∀ x : Fin 4060, m97 x.val = Part6Nat.force m45 (m68 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp98 : CompositionCheck 94 := by
  change ∀ x : Fin 4060, m98 x.val = Part6Nat.force m2 (m9 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp99 : CompositionCheck 95 := by
  change ∀ x : Fin 4060, m99 x.val = Part6Nat.force m44 (m68 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp100 : CompositionCheck 96 := by
  change ∀ x : Fin 4060, m100 x.val = Part6Nat.force m80 (m4 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp101 : CompositionCheck 97 := by
  change ∀ x : Fin 4060, m101 x.val = Part6Nat.force m52 (m42 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp102 : CompositionCheck 98 := by
  change ∀ x : Fin 4060, m102 x.val = Part6Nat.force m51 (m2 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp103 : CompositionCheck 99 := by
  change ∀ x : Fin 4060, m103 x.val = Part6Nat.force m102 (m47 x.val)
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp104 : CompositionCheck 100 := by
  change ∀ x : Fin 4060, m104 x.val = Part6Nat.force m81 (m34 x.val)
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block0.FactorMaps
