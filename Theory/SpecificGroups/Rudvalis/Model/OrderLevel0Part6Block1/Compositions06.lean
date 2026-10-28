module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 6

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp56 : ∀ x : Fin 4060,
    map56 x.val = Part6Nat.force map29 (map52 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp57 : ∀ x : Fin 4060,
    map57 x.val = Part6Nat.force map55 (map7 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp58 : ∀ x : Fin 4060,
    map58 x.val = Part6Nat.force map12 (map24 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp59 : ∀ x : Fin 4060,
    map59 x.val = Part6Nat.force map34 (map44 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp60 : ∀ x : Fin 4060,
    map60 x.val = Part6Nat.force map1 (map1 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp61 : ∀ x : Fin 4060,
    map61 x.val = Part6Nat.force map25 (map57 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp62 : ∀ x : Fin 4060,
    map62 x.val = Part6Nat.force map32 (map31 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp63 : ∀ x : Fin 4060,
    map63 x.val = Part6Nat.force map12 (map21 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
