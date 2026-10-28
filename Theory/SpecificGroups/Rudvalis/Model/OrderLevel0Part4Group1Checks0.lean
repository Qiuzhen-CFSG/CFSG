module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part4Group1Data
/-!
# Rudvalis group-1 compressed table checks, block 0

Kernel-check one quarter of the composition tables in `OrderLevel0Part4Group1Data`.
The blocks are independent so each kernel process has bounded working memory.
Source: the ATLAS tables and repeated factor subwords in that data module.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem check4 :
    checkFin (fun x : Fin 4060 => decide (map4 x.val = map1 (map2 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check5 :
    checkFin (fun x : Fin 4060 => decide (map5 x.val = map3 (map0 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check6 :
    checkFin (fun x : Fin 4060 => decide (map6 x.val = map3 (map2 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check7 :
    checkFin (fun x : Fin 4060 => decide (map7 x.val = map1 (map0 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check8 :
    checkFin (fun x : Fin 4060 => decide (map8 x.val = map4 (map4 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check9 :
    checkFin (fun x : Fin 4060 => decide (map9 x.val = map6 (map8 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check10 :
    checkFin (fun x : Fin 4060 => decide (map10 x.val = map6 (map9 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check11 :
    checkFin (fun x : Fin 4060 => decide (map11 x.val = map5 (map7 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check12 :
    checkFin (fun x : Fin 4060 => decide (map12 x.val = map5 (map11 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check13 :
    checkFin (fun x : Fin 4060 => decide (map13 x.val = map10 (map2 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check14 :
    checkFin (fun x : Fin 4060 => decide (map14 x.val = map7 (map12 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check15 :
    checkFin (fun x : Fin 4060 => decide (map15 x.val = map3 (map6 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check16 :
    checkFin (fun x : Fin 4060 => decide (map16 x.val = map5 (map0 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check17 :
    checkFin (fun x : Fin 4060 => decide (map17 x.val = map8 (map5 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check18 :
    checkFin (fun x : Fin 4060 => decide (map18 x.val = map16 (map12 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check19 :
    checkFin (fun x : Fin 4060 => decide (map19 x.val = map13 (map4 x.val))) = true := by
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem check20 :
    checkFin (fun x : Fin 4060 => decide (map20 x.val = map3 (map5 x.val))) = true := by
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part4Group1Fast
