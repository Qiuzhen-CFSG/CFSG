module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Composition checks for residual group 1, block 5

Each equality checks the action of one shared subword on all 4060 points.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem node13 : ∀ x, map13 x = map8 (map8 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node21 : ∀ x, map21 x = map9 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node29 : ∀ x, map29 x = map9 (map25 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node37 : ∀ x, map37 x = map33 (map32 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node45 : ∀ x, map45 x = map41 (map43 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node53 : ∀ x, map53 x = map8 (map14 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node61 : ∀ x, map61 x = map1 (map1 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node69 : ∀ x, map69 x = map24 (map13 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node77 : ∀ x, map77 x = map73 (map50 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node85 : ∀ x, map85 x = map25 (map57 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node93 : ∀ x, map93 x = map29 (map58 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node101 : ∀ x, map101 x = map29 (map57 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node109 : ∀ x, map109 x = map27 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node117 : ∀ x, map117 x = map40 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node125 : ∀ x, map125 x = map0 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node133 : ∀ x, map133 x = map24 (map98 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node141 : ∀ x, map141 x = map19 (map92 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node149 : ∀ x, map149 x = map68 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node157 : ∀ x, map157 x = map0 (map72 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node165 : ∀ x, map165 x = map19 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node173 : ∀ x, map173 x = map105 (map48 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node181 : ∀ x, map181 x = map65 (map70 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node189 : ∀ x, map189 x = map122 (map52 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node197 : ∀ x, map197 x = map10 (map21 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node205 : ∀ x, map205 x = map48 (map59 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node213 : ∀ x, map213 x = map9 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node221 : ∀ x, map221 x = map87 (map49 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node229 : ∀ x, map229 x = map115 (map228 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node237 : ∀ x, map237 x = map74 (map236 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node245 : ∀ x, map245 x = map81 (map117 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node253 : ∀ x, map253 x = map11 (map20 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node261 : ∀ x, map261 x = map258 (map260 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node269 : ∀ x, map269 x = map265 (map268 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node277 : ∀ x, map277 x = map273 (map276 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node285 : ∀ x, map285 x = map281 (map284 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node293 : ∀ x, map293 x = map289 (map292 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node301 : ∀ x, map301 x = map298 (map300 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node309 : ∀ x, map309 x = map102 (map308 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node317 : ∀ x, map317 x = map15 (map18 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node325 : ∀ x, map325 x = map81 (map140 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node333 : ∀ x, map333 x = map76 (map190 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node341 : ∀ x, map341 x = map59 (map15 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node349 : ∀ x, map349 x = map79 (map107 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node357 : ∀ x, map357 x = map355 (map356 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node365 : ∀ x, map365 x = map143 (map144 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node373 : ∀ x, map373 x = map22 (map372 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node381 : ∀ x, map381 x = map376 (map380 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node389 : ∀ x, map389 x = map60 (map113 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node397 : ∀ x, map397 x = map33 (map85 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node405 : ∀ x, map405 x = map12 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node413 : ∀ x, map413 x = map82 (map200 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node421 : ∀ x, map421 x = map40 (map72 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node429 : ∀ x, map429 x = map424 (map428 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node437 : ∀ x, map437 x = map97 (map436 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node445 : ∀ x, map445 x = map441 (map444 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node453 : ∀ x, map453 x = map451 (map452 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node461 : ∀ x, map461 x = map209 (map70 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node469 : ∀ x, map469 x = map153 (map211 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node477 : ∀ x, map477 x = map212 (map476 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node485 : ∀ x, map485 x = map481 (map484 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node493 : ∀ x, map493 x = map489 (map492 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node501 : ∀ x, map501 x = map497 (map500 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node509 : ∀ x, map509 x = map505 (map508 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node517 : ∀ x, map517 x = map216 (map516 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node525 : ∀ x, map525 x = map173 (map524 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node533 : ∀ x, map533 x = map528 (map532 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node541 : ∀ x, map541 x = map200 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node549 : ∀ x, map549 x = map8 (map93 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node557 : ∀ x, map557 x = map555 (map556 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node565 : ∀ x, map565 x = map563 (map564 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node573 : ∀ x, map573 x = map92 (map146 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node581 : ∀ x, map581 x = map66 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node589 : ∀ x, map589 x = map587 (map588 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node597 : ∀ x, map597 x = map23 (map596 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node605 : ∀ x, map605 x = map41 (map73 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node613 : ∀ x, map613 x = map610 (map612 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node621 : ∀ x, map621 x = map82 (map154 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node629 : ∀ x, map629 x = map19 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node637 : ∀ x, map637 x = map12 (map146 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node645 : ∀ x, map645 x = map3 (map7 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node653 : ∀ x, map653 x = map83 (map31 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node661 : ∀ x, map661 x = map100 (map50 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node669 : ∀ x, map669 x = map667 (map668 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node677 : ∀ x, map677 x = map112 (map144 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node685 : ∀ x, map685 x = map203 (map104 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node693 : ∀ x, map693 x = map688 (map692 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node701 : ∀ x, map701 x = map14 (map700 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node709 : ∀ x, map709 x = map92 (map197 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node717 : ∀ x, map717 x = map136 (map5 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node725 : ∀ x, map725 x = map723 (map724 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node733 : ∀ x, map733 x = map130 (map122 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node741 : ∀ x, map741 x = map114 (map182 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node749 : ∀ x, map749 x = map190 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node757 : ∀ x, map757 x = map17 (map18 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node765 : ∀ x, map765 x = map33 (map11 x) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
