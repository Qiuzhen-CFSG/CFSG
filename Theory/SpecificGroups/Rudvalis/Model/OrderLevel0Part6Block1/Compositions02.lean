module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 2

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp24 : ∀ x : Fin 4060,
    map24 x.val = Part6Nat.force map1 (map12 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp25 : ∀ x : Fin 4060,
    map25 x.val = Part6Nat.force map17 (map16 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp26 : ∀ x : Fin 4060,
    map26 x.val = Part6Nat.force map7 (map10 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp27 : ∀ x : Fin 4060,
    map27 x.val = Part6Nat.force map8 (map17 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp28 : ∀ x : Fin 4060,
    map28 x.val = Part6Nat.force map7 (map9 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp29 : ∀ x : Fin 4060,
    map29 x.val = Part6Nat.force map13 (map9 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp30 : ∀ x : Fin 4060,
    map30 x.val = Part6Nat.force map8 (map9 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp31 : ∀ x : Fin 4060,
    map31 x.val = Part6Nat.force map23 (map25 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
