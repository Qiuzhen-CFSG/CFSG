module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Data
/-!
# Rudvalis group-1 compressed table checks, block 3

Kernel-check one quarter of the composition tables in `OrderLevel0Part4Group1Data`.
The blocks are independent so each kernel process has bounded working memory.
Source: the ATLAS tables and repeated factor subwords in that data module.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem check55 :
    checkFin (fun x : Fin 4060 => decide (map55 x.val = map30 (map52 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check56 :
    checkFin (fun x : Fin 4060 => decide (map56 x.val = map40 (map1 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check57 :
    checkFin (fun x : Fin 4060 => decide (map57 x.val = map10 (map43 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check58 :
    checkFin (fun x : Fin 4060 => decide (map58 x.val = map47 (map37 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check59 :
    checkFin (fun x : Fin 4060 => decide (map59 x.val = map19 (map2 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check60 :
    checkFin (fun x : Fin 4060 => decide (map60 x.val = map39 (map39 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check61 :
    checkFin (fun x : Fin 4060 => decide (map61 x.val = map4 (map1 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check62 :
    checkFin (fun x : Fin 4060 => decide (map62 x.val = map21 (map53 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check63 :
    checkFin (fun x : Fin 4060 => decide (map63 x.val = map0 (map7 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check64 :
    checkFin (fun x : Fin 4060 => decide (map64 x.val = map2 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check65 :
    checkFin (fun x : Fin 4060 => decide (map65 x.val = map14 (map17 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check66 :
    checkFin (fun x : Fin 4060 => decide (map66 x.val = map27 (map24 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check67 :
    checkFin (fun x : Fin 4060 => decide (map67 x.val = map26 (map21 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check68 :
    checkFin (fun x : Fin 4060 => decide (map68 x.val = map26 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check69 :
    checkFin (fun x : Fin 4060 => decide (map69 x.val = map59 (map62 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check70 :
    checkFin (fun x : Fin 4060 => decide (map70 x.val = map33 (map39 x.val))) = true := by
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
