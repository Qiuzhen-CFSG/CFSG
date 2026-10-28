module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 3

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp32 : ∀ x : Fin 4060,
    map32 x.val = Part6Nat.force map22 (map30 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp33 : ∀ x : Fin 4060,
    map33 x.val = Part6Nat.force map1 (map19 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp34 : ∀ x : Fin 4060,
    map34 x.val = Part6Nat.force map26 (map28 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp35 : ∀ x : Fin 4060,
    map35 x.val = Part6Nat.force map5 (map29 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp36 : ∀ x : Fin 4060,
    map36 x.val = Part6Nat.force map5 (map11 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp37 : ∀ x : Fin 4060,
    map37 x.val = Part6Nat.force map34 (map5 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp38 : ∀ x : Fin 4060,
    map38 x.val = Part6Nat.force map36 (map35 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp39 : ∀ x : Fin 4060,
    map39 x.val = Part6Nat.force map38 (map32 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
