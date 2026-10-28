module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 4

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp40 : ∀ x : Fin 4060,
    map40 x.val = Part6Nat.force map11 (map20 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp41 : ∀ x : Fin 4060,
    map41 x.val = Part6Nat.force map26 (map39 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp42 : ∀ x : Fin 4060,
    map42 x.val = Part6Nat.force map18 (map22 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp43 : ∀ x : Fin 4060,
    map43 x.val = Part6Nat.force map41 (map18 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp44 : ∀ x : Fin 4060,
    map44 x.val = Part6Nat.force map8 (map15 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp45 : ∀ x : Fin 4060,
    map45 x.val = Part6Nat.force map27 (map23 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp46 : ∀ x : Fin 4060,
    map46 x.val = Part6Nat.force map24 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp47 : ∀ x : Fin 4060,
    map47 x.val = Part6Nat.force map40 (map31 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
