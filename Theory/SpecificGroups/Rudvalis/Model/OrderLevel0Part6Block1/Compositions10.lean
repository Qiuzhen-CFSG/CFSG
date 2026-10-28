module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 10

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp88 : ∀ x : Fin 4060,
    map88 x.val = Part6Nat.force map43 (map7 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp89 : ∀ x : Fin 4060,
    map89 x.val = Part6Nat.force map33 (map33 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp90 : ∀ x : Fin 4060,
    map90 x.val = Part6Nat.force map0 (map19 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp91 : ∀ x : Fin 4060,
    map91 x.val = Part6Nat.force map6 (map17 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp92 : ∀ x : Fin 4060,
    map92 x.val = Part6Nat.force map33 (map19 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp93 : ∀ x : Fin 4060,
    map93 x.val = Part6Nat.force map7 (map15 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp94 : ∀ x : Fin 4060,
    map94 x.val = Part6Nat.force map25 (map25 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp95 : ∀ x : Fin 4060,
    map95 x.val = Part6Nat.force map19 (map3 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
