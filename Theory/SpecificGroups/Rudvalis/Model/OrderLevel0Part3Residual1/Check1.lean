module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Composition checks for residual group 1, block 1

Each equality checks the action of one shared subword on all 4060 points.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem node9 : ∀ x, map9 x = map7 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node17 : ∀ x, map17 x = map9 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node25 : ∀ x, map25 x = map7 (map10 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node33 : ∀ x, map33 x = map5 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node41 : ∀ x, map41 x = map16 (map34 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node49 : ∀ x, map49 x = map28 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node57 : ∀ x, map57 x = map30 (map53 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node65 : ∀ x, map65 x = map35 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node73 : ∀ x, map73 x = map31 (map50 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node81 : ∀ x, map81 x = map0 (map42 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node89 : ∀ x, map89 x = map39 (map36 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node97 : ∀ x, map97 x = map25 (map58 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node105 : ∀ x, map105 x = map0 (map15 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node113 : ∀ x, map113 x = map65 (map75 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node121 : ∀ x, map121 x = map0 (map59 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node129 : ∀ x, map129 x = map49 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node137 : ∀ x, map137 x = map64 (map1 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node145 : ∀ x, map145 x = map28 (map56 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node153 : ∀ x, map153 x = map26 (map51 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node161 : ∀ x, map161 x = map5 (map107 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node169 : ∀ x, map169 x = map168 (map75 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node177 : ∀ x, map177 x = map176 (map53 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node185 : ∀ x, map185 x = map0 (map106 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node193 : ∀ x, map193 x = map99 (map43 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node201 : ∀ x, map201 x = map31 (map71 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node209 : ∀ x, map209 x = map85 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node217 : ∀ x, map217 x = map102 (map69 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node225 : ∀ x, map225 x = map8 (map23 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node233 : ∀ x, map233 x = map158 (map116 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node241 : ∀ x, map241 x = map97 (map51 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node249 : ∀ x, map249 x = map42 (map132 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node257 : ∀ x, map257 x = map157 (map74 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node265 : ∀ x, map265 x = map42 (map264 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node273 : ∀ x, map273 x = map271 (map272 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node281 : ∀ x, map281 x = map279 (map280 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node289 : ∀ x, map289 x = map287 (map288 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node297 : ∀ x, map297 x = map295 (map296 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node305 : ∀ x, map305 x = map40 (map3 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node313 : ∀ x, map313 x = map84 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node321 : ∀ x, map321 x = map187 (map320 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node329 : ∀ x, map329 x = map36 (map77 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node337 : ∀ x, map337 x = map79 (map336 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node345 : ∀ x, map345 x = map81 (map344 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node353 : ∀ x, map353 x = map348 (map352 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node361 : ∀ x, map361 x = map357 (map360 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node369 : ∀ x, map369 x = map102 (map368 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node377 : ∀ x, map377 x = map112 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node385 : ∀ x, map385 x = map145 (map384 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node393 : ∀ x, map393 x = map142 (map141 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node401 : ∀ x, map401 x = map396 (map400 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node409 : ∀ x, map409 x = map407 (map408 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node417 : ∀ x, map417 x = map202 (map127 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node425 : ∀ x, map425 x = map114 (map107 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node433 : ∀ x, map433 x = map203 (map117 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node441 : ∀ x, map441 x = map42 (map440 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node449 : ∀ x, map449 x = map4 (map88 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node457 : ∀ x, map457 x = map208 (map56 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node465 : ∀ x, map465 x = map151 (map95 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node473 : ∀ x, map473 x = map22 (map472 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node481 : ∀ x, map481 x = map185 (map480 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node489 : ∀ x, map489 x = map487 (map488 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node497 : ∀ x, map497 x = map495 (map496 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node505 : ∀ x, map505 x = map503 (map504 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node513 : ∀ x, map513 x = map96 (map144 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node521 : ∀ x, map521 x = map76 (map520 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node529 : ∀ x, map529 x = map91 (map126 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node537 : ∀ x, map537 x = map216 (map181 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node545 : ∀ x, map545 x = map87 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node553 : ∀ x, map553 x = map548 (map552 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node561 : ∀ x, map561 x = map557 (map560 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node569 : ∀ x, map569 x = map566 (map568 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node577 : ∀ x, map577 x = map575 (map576 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node585 : ∀ x, map585 x = map111 (map17 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node593 : ∀ x, map593 x = map165 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node601 : ∀ x, map601 x = map0 (map129 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node609 : ∀ x, map609 x = map142 (map104 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node617 : ∀ x, map617 x = map614 (map616 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node625 : ∀ x, map625 x = map36 (map127 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node633 : ∀ x, map633 x = map631 (map632 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node641 : ∀ x, map641 x = map639 (map640 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node649 : ∀ x, map649 x = map210 (map88 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node657 : ∀ x, map657 x = map19 (map40 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node665 : ∀ x, map665 x = map74 (map143 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node673 : ∀ x, map673 x = map669 (map672 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node681 : ∀ x, map681 x = map54 (map680 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node689 : ∀ x, map689 x = map11 (map102 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node697 : ∀ x, map697 x = map4 (map213 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node705 : ∀ x, map705 x = map699 (map704 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node713 : ∀ x, map713 x = map183 (map712 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node721 : ∀ x, map721 x = map208 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node729 : ∀ x, map729 x = map40 (map82 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node737 : ∀ x, map737 x = map732 (map736 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node745 : ∀ x, map745 x = map743 (map744 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node753 : ∀ x, map753 x = map750 (map752 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node761 : ∀ x, map761 x = map170 (map87 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node769 : ∀ x, map769 x = map764 (map768 x) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
