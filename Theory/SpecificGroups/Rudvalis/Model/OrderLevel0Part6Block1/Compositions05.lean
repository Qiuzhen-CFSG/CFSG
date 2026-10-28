module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 5

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp48 : ∀ x : Fin 4060,
    map48 x.val = Part6Nat.force map37 (map27 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp49 : ∀ x : Fin 4060,
    map49 x.val = Part6Nat.force map43 (map42 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp50 : ∀ x : Fin 4060,
    map50 x.val = Part6Nat.force map12 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp51 : ∀ x : Fin 4060,
    map51 x.val = Part6Nat.force map21 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp52 : ∀ x : Fin 4060,
    map52 x.val = Part6Nat.force map49 (map47 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp53 : ∀ x : Fin 4060,
    map53 x.val = Part6Nat.force map10 (map28 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp54 : ∀ x : Fin 4060,
    map54 x.val = Part6Nat.force map45 (map27 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp55 : ∀ x : Fin 4060,
    map55 x.val = Part6Nat.force map54 (map48 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
