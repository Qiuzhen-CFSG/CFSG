module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Composition checks for residual group 1, block 0

Each equality checks the action of one shared subword on all 4060 points.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem node8 : ∀ x, map8 x = map5 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node16 : ∀ x, map16 x = map10 (map14 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node24 : ∀ x, map24 x = map21 (map18 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node32 : ∀ x, map32 x = map5 (map13 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node40 : ∀ x, map40 x = map15 (map15 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node48 : ∀ x, map48 x = map1 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node56 : ∀ x, map56 x = map12 (map3 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node64 : ∀ x, map64 x = map1 (map28 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node72 : ∀ x, map72 x = map15 (map42 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node80 : ∀ x, map80 x = map28 (map28 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node88 : ∀ x, map88 x = map4 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node96 : ∀ x, map96 x = map28 (map1 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node104 : ∀ x, map104 x = map48 (map61 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node112 : ∀ x, map112 x = map33 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node120 : ∀ x, map120 x = map22 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node128 : ∀ x, map128 x = map0 (map66 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node136 : ∀ x, map136 x = map86 (map3 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node144 : ∀ x, map144 x = map33 (map8 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node152 : ∀ x, map152 x = map71 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node160 : ∀ x, map160 x = map131 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node168 : ∀ x, map168 x = map167 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node176 : ∀ x, map176 x = map9 (map5 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node184 : ∀ x, map184 x = map41 (map77 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node192 : ∀ x, map192 x = map76 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node200 : ∀ x, map200 x = map42 (map12 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node208 : ∀ x, map208 x = map40 (map49 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node216 : ∀ x, map216 x = map24 (map155 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node224 : ∀ x, map224 x = map15 (map95 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node232 : ∀ x, map232 x = map27 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node240 : ∀ x, map240 x = map14 (map85 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node248 : ∀ x, map248 x = map245 (map247 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node256 : ∀ x, map256 x = map252 (map255 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node264 : ∀ x, map264 x = map136 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node272 : ∀ x, map272 x = map171 (map88 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node280 : ∀ x, map280 x = map175 (map177 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node288 : ∀ x, map288 x = map108 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node296 : ∀ x, map296 x = map11 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node304 : ∀ x, map304 x = map138 (map42 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node312 : ∀ x, map312 x = map120 (map74 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node320 : ∀ x, map320 x = map34 (map116 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node328 : ∀ x, map328 x = map53 (map16 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node336 : ∀ x, map336 x = map139 (map162 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node344 : ∀ x, map344 x = map42 (map123 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node352 : ∀ x, map352 x = map349 (map351 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node360 : ∀ x, map360 x = map358 (map359 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node368 : ∀ x, map368 x = map65 (map77 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node376 : ∀ x, map376 x = map374 (map375 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node384 : ∀ x, map384 x = map146 (map195 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node392 : ∀ x, map392 x = map386 (map391 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node400 : ∀ x, map400 x = map397 (map399 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node408 : ∀ x, map408 x = map199 (map166 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node416 : ∀ x, map416 x = map27 (map201 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node424 : ∀ x, map424 x = map421 (map423 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node432 : ∀ x, map432 x = map22 (map431 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node440 : ∀ x, map440 x = map129 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node448 : ∀ x, map448 x = map129 (map103 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node456 : ∀ x, map456 x = map0 (map455 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node464 : ∀ x, map464 x = map0 (map210 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node472 : ∀ x, map472 x = map66 (map59 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node480 : ∀ x, map480 x = map56 (map213 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node488 : ∀ x, map488 x = map132 (map215 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node496 : ∀ x, map496 x = map48 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node504 : ∀ x, map504 x = map4 (map215 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node512 : ∀ x, map512 x = map66 (map66 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node520 : ∀ x, map520 x = map42 (map156 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node528 : ∀ x, map528 x = map526 (map527 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node536 : ∀ x, map536 x = map221 (map535 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node544 : ∀ x, map544 x = map0 (map543 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node552 : ∀ x, map552 x = map549 (map551 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node560 : ∀ x, map560 x = map558 (map559 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node568 : ∀ x, map568 x = map71 (map567 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node576 : ∀ x, map576 x = map34 (map94 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node584 : ∀ x, map584 x = map48 (map583 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node592 : ∀ x, map592 x = map15 (map106 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node600 : ∀ x, map600 x = map198 (map104 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node608 : ∀ x, map608 x = map603 (map607 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node616 : ∀ x, map616 x = map35 (map615 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node624 : ∀ x, map624 x = map153 (map52 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node632 : ∀ x, map632 x = map13 (map218 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node640 : ∀ x, map640 x = map172 (map45 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node648 : ∀ x, map648 x = map76 (map647 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node656 : ∀ x, map656 x = map128 (map136 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node664 : ∀ x, map664 x = map659 (map663 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node672 : ∀ x, map672 x = map670 (map671 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node680 : ∀ x, map680 x = map60 (map63 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node688 : ∀ x, map688 x = map685 (map687 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node696 : ∀ x, map696 x = map40 (map111 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node704 : ∀ x, map704 x = map701 (map703 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node712 : ∀ x, map712 x = map34 (map77 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node720 : ∀ x, map720 x = map19 (map719 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node728 : ∀ x, map728 x = map147 (map727 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node736 : ∀ x, map736 x = map733 (map735 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node744 : ∀ x, map744 x = map202 (map227 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node752 : ∀ x, map752 x = map118 (map751 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node760 : ∀ x, map760 x = map756 (map759 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node768 : ∀ x, map768 x = map765 (map767 x) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
