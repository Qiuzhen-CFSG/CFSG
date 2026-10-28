module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Composition checks for residual group 1, block 4

Each equality checks the action of one shared subword on all 4060 points.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem node12 : ∀ x, map12 x = map1 (map0 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node20 : ∀ x, map20 x = map9 (map16 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node28 : ∀ x, map28 x = map12 (map1 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node36 : ∀ x, map36 x = map20 (map26 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node44 : ∀ x, map44 x = map30 (map5 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node52 : ∀ x, map52 x = map23 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node60 : ∀ x, map60 x = map54 (map55 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node68 : ∀ x, map68 x = map28 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node76 : ∀ x, map76 x = map0 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node84 : ∀ x, map84 x = map15 (map61 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node92 : ∀ x, map92 x = map1 (map12 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node100 : ∀ x, map100 x = map23 (map23 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node108 : ∀ x, map108 x = map4 (map10 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node116 : ∀ x, map116 x = map65 (map31 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node124 : ∀ x, map124 x = map90 (map50 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node132 : ∀ x, map132 x = map15 (map56 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node140 : ∀ x, map140 x = map80 (map56 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node148 : ∀ x, map148 x = map4 (map17 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node156 : ∀ x, map156 x = map22 (map61 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node164 : ∀ x, map164 x = map42 (map42 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node172 : ∀ x, map172 x = map54 (map101 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node180 : ∀ x, map180 x = map76 (map72 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node188 : ∀ x, map188 x = map78 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node196 : ∀ x, map196 x = map31 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node204 : ∀ x, map204 x = map72 (map22 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node212 : ∀ x, map212 x = map114 (map27 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node220 : ∀ x, map220 x = map219 (map84 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node228 : ∀ x, map228 x = map42 (map3 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node236 : ∀ x, map236 x = map22 (map56 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node244 : ∀ x, map244 x = map106 (map132 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node252 : ∀ x, map252 x = map81 (map251 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node260 : ∀ x, map260 x = map16 (map259 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node268 : ∀ x, map268 x = map266 (map267 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node276 : ∀ x, map276 x = map274 (map275 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node284 : ∀ x, map284 x = map282 (map283 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node292 : ∀ x, map292 x = map290 (map291 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node300 : ∀ x, map300 x = map54 (map299 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node308 : ∀ x, map308 x = map183 (map184 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node316 : ∀ x, map316 x = map121 (map66 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node324 : ∀ x, map324 x = map19 (map188 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node332 : ∀ x, map332 x = map327 (map331 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node340 : ∀ x, map340 x = map121 (map339 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node348 : ∀ x, map348 x = map346 (map347 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node356 : ∀ x, map356 x = map34 (map108 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node364 : ∀ x, map364 x = map40 (map78 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node372 : ∀ x, map372 x = map49 (map123 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node380 : ∀ x, map380 x = map377 (map379 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node388 : ∀ x, map388 x = map13 (map387 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node396 : ∀ x, map396 x = map394 (map395 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node404 : ∀ x, map404 x = map125 (map82 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node412 : ∀ x, map412 x = map147 (map411 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node420 : ∀ x, map420 x = map128 (map115 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node428 : ∀ x, map428 x = map425 (map427 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node436 : ∀ x, map436 x = map93 (map113 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node444 : ∀ x, map444 x = map442 (map443 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node452 : ∀ x, map452 x = map38 (map207 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node460 : ∀ x, map460 x = map9 (map130 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node468 : ∀ x, map468 x = map152 (map101 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node476 : ∀ x, map476 x = map196 (map191 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node484 : ∀ x, map484 x = map482 (map483 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node492 : ∀ x, map492 x = map490 (map491 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node500 : ∀ x, map500 x = map498 (map499 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node508 : ∀ x, map508 x = map506 (map507 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node516 : ∀ x, map516 x = map55 (map63 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node524 : ∀ x, map524 x = map19 (map84 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node532 : ∀ x, map532 x = map529 (map531 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node540 : ∀ x, map540 x = map180 (map84 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node548 : ∀ x, map548 x = map545 (map547 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node556 : ∀ x, map556 x = map4 (map79 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node564 : ∀ x, map564 x = map92 (map88 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node572 : ∀ x, map572 x = map82 (map40 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node580 : ∀ x, map580 x = map22 (map579 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node588 : ∀ x, map588 x = map93 (map194 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node596 : ∀ x, map596 x = map206 (map207 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node604 : ∀ x, map604 x = map9 (map71 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node612 : ∀ x, map612 x = map74 (map611 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node620 : ∀ x, map620 x = map0 (map619 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node628 : ∀ x, map628 x = map128 (map224 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node636 : ∀ x, map636 x = map226 (map68 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node644 : ∀ x, map644 x = map59 (map82 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node652 : ∀ x, map652 x = map69 (map101 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node660 : ∀ x, map660 x = map53 (map8 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node668 : ∀ x, map668 x = map171 (map212 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node676 : ∀ x, map676 x = map66 (map179 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node684 : ∀ x, map684 x = map49 (map140 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node692 : ∀ x, map692 x = map689 (map691 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node700 : ∀ x, map700 x = map41 (map51 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node708 : ∀ x, map708 x = map59 (map68 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node716 : ∀ x, map716 x = map111 (map95 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node724 : ∀ x, map724 x = map99 (map169 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node732 : ∀ x, map732 x = map729 (map731 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node740 : ∀ x, map740 x = map226 (map174 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node748 : ∀ x, map748 x = map81 (map747 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node756 : ∀ x, map756 x = map220 (map755 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node764 : ∀ x, map764 x = map762 (map763 x) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
