module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Composition checks for residual group 1, block 3

Each equality checks the action of one shared subword on all 4060 points.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem node11 : ∀ x, map11 x = map5 (map4 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node19 : ∀ x, map19 x = map12 (map12 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node27 : ∀ x, map27 x = map8 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node35 : ∀ x, map35 x = map20 (map16 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node43 : ∀ x, map43 x = map4 (map31 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node51 : ∀ x, map51 x = map29 (map44 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node59 : ∀ x, map59 x = map15 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node67 : ∀ x, map67 x = map62 (map63 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node75 : ∀ x, map75 x = map6 (map70 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node83 : ∀ x, map83 x = map16 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node91 : ∀ x, map91 x = map4 (map8 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node99 : ∀ x, map99 x = map35 (map34 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node107 : ∀ x, map107 x = map5 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node115 : ∀ x, map115 x = map48 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node123 : ∀ x, map123 x = map28 (map12 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node131 : ∀ x, map131 x = map9 (map10 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node139 : ∀ x, map139 x = map10 (map32 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node147 : ∀ x, map147 x = map0 (map48 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node155 : ∀ x, map155 x = map71 (map52 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node163 : ∀ x, map163 x = map99 (map31 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node171 : ∀ x, map171 x = map4 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node179 : ∀ x, map179 x = map86 (map15 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node187 : ∀ x, map187 x = map186 (map110 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node195 : ∀ x, map195 x = map10 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node203 : ∀ x, map203 x = map0 (map49 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node211 : ∀ x, map211 x = map62 (map113 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node219 : ∀ x, map219 x = map64 (map49 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node227 : ∀ x, map227 x = map47 (map50 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node235 : ∀ x, map235 x = map231 (map234 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node243 : ∀ x, map243 x = map239 (map242 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node251 : ∀ x, map251 x = map82 (map135 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node259 : ∀ x, map259 x = map135 (map166 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node267 : ∀ x, map267 x = map52 (map169 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node275 : ∀ x, map275 x = map97 (map90 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node283 : ∀ x, map283 x = map102 (map31 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node291 : ∀ x, map291 x = map101 (map119 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node299 : ∀ x, map299 x = map54 (map181 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node307 : ∀ x, map307 x = map182 (map139 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node315 : ∀ x, map315 x = map48 (map178 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node323 : ∀ x, map323 x = map318 (map322 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node331 : ∀ x, map331 x = map328 (map330 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node339 : ∀ x, map339 x = map48 (map103 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node347 : ∀ x, map347 x = map3 (map91 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node355 : ∀ x, map355 x = map142 (map137 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node363 : ∀ x, map363 x = map42 (map362 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node371 : ∀ x, map371 x = map366 (map370 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node379 : ∀ x, map379 x = map134 (map378 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node387 : ∀ x, map387 x = map16 (map41 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node395 : ∀ x, map395 x = map12 (map197 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node403 : ∀ x, map403 x = map198 (map402 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node411 : ∀ x, map411 x = map19 (map59 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node419 : ∀ x, map419 x = map415 (map418 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node427 : ∀ x, map427 x = map93 (map426 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node435 : ∀ x, map435 x = map204 (map434 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node443 : ∀ x, map443 x = map206 (map94 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node451 : ∀ x, map451 x = map10 (map8 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node459 : ∀ x, map459 x = map457 (map458 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node467 : ∀ x, map467 x = map465 (map466 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node475 : ∀ x, map475 x = map159 (map474 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node483 : ∀ x, map483 x = map214 (map211 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node491 : ∀ x, map491 x = map69 (map127 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node499 : ∀ x, map499 x = map97 (map124 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node507 : ∀ x, map507 x = map16 (map7 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node515 : ∀ x, map515 x = map5 (map33 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node523 : ∀ x, map523 x = map120 (map522 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node531 : ∀ x, map531 x = map26 (map530 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node539 : ∀ x, map539 x = map536 (map538 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node547 : ∀ x, map547 x = map15 (map546 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node555 : ∀ x, map555 x = map222 (map66 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node563 : ∀ x, map563 x = map59 (map59 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node571 : ∀ x, map571 x = map106 (map156 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node579 : ∀ x, map579 x = map78 (map84 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node587 : ∀ x, map587 x = map21 (map152 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node595 : ∀ x, map595 x = map10 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node603 : ∀ x, map603 x = map601 (map602 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node611 : ∀ x, map611 x = map126 (map195 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node619 : ∀ x, map619 x = map80 (map140 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node627 : ∀ x, map627 x = map623 (map626 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node635 : ∀ x, map635 x = map222 (map95 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node643 : ∀ x, map643 x = map121 (map224 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node651 : ∀ x, map651 x = map649 (map650 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node659 : ∀ x, map659 x = map657 (map658 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node667 : ∀ x, map667 x = map151 (map154 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node675 : ∀ x, map675 x = map128 (map674 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node683 : ∀ x, map683 x = map678 (map682 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node691 : ∀ x, map691 x = map101 (map690 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node699 : ∀ x, map699 x = map696 (map698 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node707 : ∀ x, map707 x = map19 (map706 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node715 : ∀ x, map715 x = map710 (map714 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node723 : ∀ x, map723 x = map88 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node731 : ∀ x, map731 x = map84 (map730 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node739 : ∀ x, map739 x = map0 (map738 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node747 : ∀ x, map747 x = map19 (map49 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node755 : ∀ x, map755 x = map88 (map108 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node763 : ∀ x, map763 x = map145 (map109 x) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
