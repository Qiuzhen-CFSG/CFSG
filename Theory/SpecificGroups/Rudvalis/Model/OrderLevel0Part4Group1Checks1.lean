module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Data
/-!
# Rudvalis group-1 compressed table checks, block 1

Kernel-check one quarter of the composition tables in `OrderLevel0Part4Group1Data`.
The blocks are independent so each kernel process has bounded working memory.
Source: the ATLAS tables and repeated factor subwords in that data module.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem check21 :
    checkFin (fun x : Fin 4060 => decide (map21 x.val = map18 (map14 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check22 :
    checkFin (fun x : Fin 4060 => decide (map22 x.val = map19 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check23 :
    checkFin (fun x : Fin 4060 => decide (map23 x.val = map4 (map7 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check24 :
    checkFin (fun x : Fin 4060 => decide (map24 x.val = map1 (map17 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check25 :
    checkFin (fun x : Fin 4060 => decide (map25 x.val = map1 (map7 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check26 :
    checkFin (fun x : Fin 4060 => decide (map26 x.val = map13 (map7 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check27 :
    checkFin (fun x : Fin 4060 => decide (map27 x.val = map15 (map20 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check28 :
    checkFin (fun x : Fin 4060 => decide (map28 x.val = map24 (map22 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check29 :
    checkFin (fun x : Fin 4060 => decide (map29 x.val = map15 (map25 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check30 :
    checkFin (fun x : Fin 4060 => decide (map30 x.val = map29 (map28 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check31 :
    checkFin (fun x : Fin 4060 => decide (map31 x.val = map10 (map10 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check32 :
    checkFin (fun x : Fin 4060 => decide (map32 x.val = map0 (map21 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check33 :
    checkFin (fun x : Fin 4060 => decide (map33 x.val = map26 (map32 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check34 :
    checkFin (fun x : Fin 4060 => decide (map34 x.val = map23 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check35 :
    checkFin (fun x : Fin 4060 => decide (map35 x.val = map30 (map31 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check36 :
    checkFin (fun x : Fin 4060 => decide (map36 x.val = map35 (map33 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check37 :
    checkFin (fun x : Fin 4060 => decide (map37 x.val = map4 (map9 x.val))) = true := by
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
