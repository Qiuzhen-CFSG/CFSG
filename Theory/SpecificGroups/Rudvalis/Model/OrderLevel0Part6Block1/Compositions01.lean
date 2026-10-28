module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 1

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp16 : ∀ x : Fin 4060,
    map16 x.val = Part6Nat.force map9 (map11 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp17 : ∀ x : Fin 4060,
    map17 x.val = Part6Nat.force map11 (map9 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp18 : ∀ x : Fin 4060,
    map18 x.val = Part6Nat.force map10 (map15 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp19 : ∀ x : Fin 4060,
    map19 x.val = Part6Nat.force map12 (map12 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp20 : ∀ x : Fin 4060,
    map20 x.val = Part6Nat.force map4 (map9 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp21 : ∀ x : Fin 4060,
    map21 x.val = Part6Nat.force map14 (map14 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp22 : ∀ x : Fin 4060,
    map22 x.val = Part6Nat.force map18 (map6 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp23 : ∀ x : Fin 4060,
    map23 x.val = Part6Nat.force map20 (map16 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
