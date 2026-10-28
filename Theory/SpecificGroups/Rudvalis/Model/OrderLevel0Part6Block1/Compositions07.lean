module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 7

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp64 : ∀ x : Fin 4060,
    map64 x.val = Part6Nat.force map24 (map21 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp65 : ∀ x : Fin 4060,
    map65 x.val = Part6Nat.force map19 (map19 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp66 : ∀ x : Fin 4060,
    map66 x.val = Part6Nat.force map12 (map33 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp67 : ∀ x : Fin 4060,
    map67 x.val = Part6Nat.force map0 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp68 : ∀ x : Fin 4060,
    map68 x.val = Part6Nat.force map6 (map9 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp69 : ∀ x : Fin 4060,
    map69 x.val = Part6Nat.force map33 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp70 : ∀ x : Fin 4060,
    map70 x.val = Part6Nat.force map18 (map62 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp71 : ∀ x : Fin 4060,
    map71 x.val = Part6Nat.force map53 (map35 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
