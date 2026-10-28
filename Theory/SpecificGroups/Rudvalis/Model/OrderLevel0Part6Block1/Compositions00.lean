module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 0

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp8 : ∀ x : Fin 4060,
    map8 x.val = Part6Nat.force map5 (map6 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp9 : ∀ x : Fin 4060,
    map9 x.val = Part6Nat.force map7 (map4 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp10 : ∀ x : Fin 4060,
    map10 x.val = Part6Nat.force map7 (map6 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp11 : ∀ x : Fin 4060,
    map11 x.val = Part6Nat.force map5 (map4 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp12 : ∀ x : Fin 4060,
    map12 x.val = Part6Nat.force map1 (map0 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp13 : ∀ x : Fin 4060,
    map13 x.val = Part6Nat.force map8 (map8 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp14 : ∀ x : Fin 4060,
    map14 x.val = Part6Nat.force map3 (map0 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp15 : ∀ x : Fin 4060,
    map15 x.val = Part6Nat.force map10 (map13 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
