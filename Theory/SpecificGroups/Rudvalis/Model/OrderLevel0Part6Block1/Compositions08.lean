module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 8

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp72 : ∀ x : Fin 4060,
    map72 x.val = Part6Nat.force map68 (map31 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp73 : ∀ x : Fin 4060,
    map73 x.val = Part6Nat.force map72 (map61 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp74 : ∀ x : Fin 4060,
    map74 x.val = Part6Nat.force map53 (map44 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp75 : ∀ x : Fin 4060,
    map75 x.val = Part6Nat.force map24 (map24 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp76 : ∀ x : Fin 4060,
    map76 x.val = Part6Nat.force map51 (map3 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp77 : ∀ x : Fin 4060,
    map77 x.val = Part6Nat.force map19 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp78 : ∀ x : Fin 4060,
    map78 x.val = Part6Nat.force map19 (map12 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp79 : ∀ x : Fin 4060,
    map79 x.val = Part6Nat.force map4 (map11 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
