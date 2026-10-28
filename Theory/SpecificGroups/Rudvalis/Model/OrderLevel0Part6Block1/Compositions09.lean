module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Data
/-!
# Rudvalis compressed table compositions, group 9

Each equation checks all 4060 points in Lean's kernel. The Python-generated
tables come from the ATLAS generators recorded in `OrderChainData` and the
repeated subwords of `OrderLevel0Data`; they carry no external trust.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem comp80 : ∀ x : Fin 4060,
    map80 x.val = Part6Nat.force map5 (map25 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp81 : ∀ x : Fin 4060,
    map81 x.val = Part6Nat.force map70 (map56 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp82 : ∀ x : Fin 4060,
    map82 x.val = Part6Nat.force map24 (map33 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp83 : ∀ x : Fin 4060,
    map83 x.val = Part6Nat.force map34 (map35 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp84 : ∀ x : Fin 4060,
    map84 x.val = Part6Nat.force map6 (map30 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp85 : ∀ x : Fin 4060,
    map85 x.val = Part6Nat.force map22 (map17 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp86 : ∀ x : Fin 4060,
    map86 x.val = Part6Nat.force map8 (map73 x.val) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem comp87 : ∀ x : Fin 4060,
    map87 x.val = Part6Nat.force map0 (map21 x.val) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part6Block1.Compressed
