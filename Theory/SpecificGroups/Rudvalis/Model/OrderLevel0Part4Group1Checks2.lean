module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Data
/-!
# Rudvalis group-1 compressed table checks, block 2

Kernel-check one quarter of the composition tables in `OrderLevel0Part4Group1Data`.
The blocks are independent so each kernel process has bounded working memory.
Source: the ATLAS tables and repeated factor subwords in that data module.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem check38 :
    checkFin (fun x : Fin 4060 => decide (map38 x.val = map27 (map1 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check39 :
    checkFin (fun x : Fin 4060 => decide (map39 x.val = map17 (map36 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check40 :
    checkFin (fun x : Fin 4060 => decide (map40 x.val = map6 (map20 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check41 :
    checkFin (fun x : Fin 4060 => decide (map41 x.val = map38 (map34 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check42 :
    checkFin (fun x : Fin 4060 => decide (map42 x.val = map27 (map37 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check43 :
    checkFin (fun x : Fin 4060 => decide (map43 x.val = map19 (map21 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check44 :
    checkFin (fun x : Fin 4060 => decide (map44 x.val = map4 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check45 :
    checkFin (fun x : Fin 4060 => decide (map45 x.val = map23 (map18 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check46 :
    checkFin (fun x : Fin 4060 => decide (map46 x.val = map34 (map41 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check47 :
    checkFin (fun x : Fin 4060 => decide (map47 x.val = map14 (map40 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check48 :
    checkFin (fun x : Fin 4060 => decide (map48 x.val = map14 (map45 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check49 :
    checkFin (fun x : Fin 4060 => decide (map49 x.val = map48 (map46 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check50 :
    checkFin (fun x : Fin 4060 => decide (map50 x.val = map2 (map44 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check51 :
    checkFin (fun x : Fin 4060 => decide (map51 x.val = map0 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check52 :
    checkFin (fun x : Fin 4060 => decide (map52 x.val = map22 (map36 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check53 :
    checkFin (fun x : Fin 4060 => decide (map53 x.val = map49 (map3 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check54 :
    checkFin (fun x : Fin 4060 => decide (map54 x.val = map2 (map7 x.val))) = true := by
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
