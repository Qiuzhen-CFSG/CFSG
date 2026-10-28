module

public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part3Residual1.Data

/-!
# Composition checks for residual group 1, block 2

Each equality checks the action of one shared subword on all 4060 points.
Source: the ATLAS witnesses in `OrderLevel0Data`, `OrderChainData`, and
`Part3Residual.target`. `GenerateCompositions.py` supplies only witnesses;
all lookup comparisons and table compositions are checked by Lean's kernel.
-/

namespace Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
set_option maxRecDepth 30000
set_option Elab.async false

set_option maxHeartbeats 1600000 in
public theorem node10 : ∀ x, map10 x = map7 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node18 : ∀ x, map18 x = map9 (map17 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node26 : ∀ x, map26 x = map6 (map8 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node34 : ∀ x, map34 x = map6 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node42 : ∀ x, map42 x = map1 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node50 : ∀ x, map50 x = map13 (map47 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node58 : ∀ x, map58 x = map30 (map32 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node66 : ∀ x, map66 x = map15 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node74 : ∀ x, map74 x = map19 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node82 : ∀ x, map82 x = map40 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node90 : ∀ x, map90 x = map89 (map47 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node98 : ∀ x, map98 x = map10 (map58 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node106 : ∀ x, map106 x = map28 (map49 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node114 : ∀ x, map114 x = map11 (map11 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node122 : ∀ x, map122 x = map25 (map44 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node130 : ∀ x, map130 x = map27 (map20 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node138 : ∀ x, map138 x = map0 (map40 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node146 : ∀ x, map146 x = map4 (map21 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node154 : ∀ x, map154 x = map40 (map96 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node162 : ∀ x, map162 x = map134 (map116 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node170 : ∀ x, map170 x = map0 (map68 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node178 : ∀ x, map178 x = map49 (map19 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node186 : ∀ x, map186 x = map100 (map23 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node194 : ∀ x, map194 x = map193 (map50 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node202 : ∀ x, map202 x = map23 (map98 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node210 : ∀ x, map210 x = map74 (map68 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node218 : ∀ x, map218 x = map217 (map124 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node226 : ∀ x, map226 x = map15 (map64 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node234 : ∀ x, map234 x = map232 (map233 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node242 : ∀ x, map242 x = map240 (map241 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node250 : ∀ x, map250 x = map48 (map249 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node258 : ∀ x, map258 x = map164 (map165 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node266 : ∀ x, map266 x = map160 (map100 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node274 : ∀ x, map274 x = map118 (map172 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node282 : ∀ x, map282 x = map26 (map55 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node290 : ∀ x, map290 x = map118 (map99 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node298 : ∀ x, map298 x = map9 (map109 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node306 : ∀ x, map306 x = map304 (map305 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node314 : ∀ x, map314 x = map185 (map313 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node322 : ∀ x, map322 x = map319 (map321 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node330 : ∀ x, map330 x = map189 (map329 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node338 : ∀ x, map338 x = map335 (map337 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node346 : ∀ x, map346 x = map59 (map78 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node354 : ∀ x, map354 x = map192 (map141 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node362 : ∀ x, map362 x = map111 (map12 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node370 : ∀ x, map370 x = map367 (map369 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node378 : ∀ x, map378 x = map6 (map124 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node386 : ∀ x, map386 x = map383 (map385 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node394 : ∀ x, map394 x = map0 (map188 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node402 : ∀ x, map402 x = map15 (map123 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node410 : ∀ x, map410 x = map406 (map409 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node418 : ∀ x, map418 x = map416 (map417 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node426 : ∀ x, map426 x = map201 (map67 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node434 : ∀ x, map434 x = map103 (map148 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node442 : ∀ x, map442 x = map10 (map112 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node450 : ∀ x, map450 x = map448 (map449 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node458 : ∀ x, map458 x = map108 (map126 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node466 : ∀ x, map466 x = map148 (map91 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node474 : ∀ x, map474 x = map123 (map13 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node482 : ∀ x, map482 x = map161 (map31 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node490 : ∀ x, map490 x = map53 (map34 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node498 : ∀ x, map498 x = map32 (map110 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node506 : ∀ x, map506 x = map199 (map85 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node514 : ∀ x, map514 x = map512 (map513 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node522 : ∀ x, map522 x = map72 (map6 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node530 : ∀ x, map530 x = map36 (map218 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node538 : ∀ x, map538 x = map34 (map537 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node546 : ∀ x, map546 x = map88 (map139 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node554 : ∀ x, map554 x = map149 (map137 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node562 : ∀ x, map562 x = map164 (map156 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node570 : ∀ x, map570 x = map565 (map569 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node578 : ∀ x, map578 x = map574 (map577 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node586 : ∀ x, map586 x = map147 (map585 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node594 : ∀ x, map594 x = map592 (map593 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node602 : ∀ x, map602 x = map96 (map79 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node610 : ∀ x, map610 x = map40 (map40 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node618 : ∀ x, map618 x = map613 (map617 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node626 : ∀ x, map626 x = map624 (map625 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node634 : ∀ x, map634 x = map630 (map633 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node642 : ∀ x, map642 x = map638 (map641 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node650 : ∀ x, map650 x = map109 (map150 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node658 : ∀ x, map658 x = map59 (map3 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node666 : ∀ x, map666 x = map138 (map665 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node674 : ∀ x, map674 x = map66 (map143 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node682 : ∀ x, map682 x = map679 (map681 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node690 : ∀ x, map690 x = map16 (map184 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node698 : ∀ x, map698 x = map15 (map697 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node706 : ∀ x, map706 x = map48 (map95 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node714 : ∀ x, map714 x = map711 (map713 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node722 : ∀ x, map722 x = map138 (map721 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node730 : ∀ x, map730 x = map107 (map109 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node738 : ∀ x, map738 x = map86 (map82 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node746 : ∀ x, map746 x = map742 (map745 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node754 : ∀ x, map754 x = map0 (map221 x) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem node762 : ∀ x, map762 x = map48 (map48 x) := by
  apply allFin
  decide +kernel

end Rudvalis.OrderCertificate.ForwardReduction.Part3Residual.Certificate1
