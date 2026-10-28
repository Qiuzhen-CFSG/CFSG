module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Maps
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Ranges


/-!
# Kernel checks of the max4 point maps

Kernel reductions in ranges of 128 points establish equality with the
literal ATLAS generator words and the fixed double-coset representatives.
Source: primary ATLAS Tits max4/max8 programs and the fixed words in
`FiveOvergroups/Representatives`. See `DoubleCosetCover/source/` for generation.
-/

namespace Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max4

open Atlas1600OrderCertificate MinimumIndexCandidates
set_option Elab.async false
set_option maxRecDepth 20000

set_option maxHeartbeats 1600000 in
public theorem gen0Check0 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 0 p) = packedGen 0 (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check1 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 128 p) = packedGen 0 (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check2 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 256 p) = packedGen 0 (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check3 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 384 p) = packedGen 0 (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check4 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 512 p) = packedGen 0 (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check5 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 640 p) = packedGen 0 (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check6 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 768 p) = packedGen 0 (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check7 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 896 p) = packedGen 0 (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check8 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 1024 p) = packedGen 0 (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check9 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 1152 p) = packedGen 0 (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check10 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 1280 p) = packedGen 0 (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check11 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 1408 p) = packedGen 0 (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen0Check12 : ∀ p : Fin 128,
    genMaps 0 (rangeIndex 1600 1536 p) = packedGen 0 (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check0 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 0 p) = packedGen 1 (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check1 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 128 p) = packedGen 1 (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check2 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 256 p) = packedGen 1 (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check3 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 384 p) = packedGen 1 (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check4 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 512 p) = packedGen 1 (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check5 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 640 p) = packedGen 1 (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check6 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 768 p) = packedGen 1 (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check7 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 896 p) = packedGen 1 (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check8 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 1024 p) = packedGen 1 (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check9 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 1152 p) = packedGen 1 (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check10 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 1280 p) = packedGen 1 (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check11 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 1408 p) = packedGen 1 (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen1Check12 : ∀ p : Fin 128,
    genMaps 1 (rangeIndex 1600 1536 p) = packedGen 1 (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check0 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 0 p) = packedGen 2 (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check1 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 128 p) = packedGen 2 (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check2 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 256 p) = packedGen 2 (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check3 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 384 p) = packedGen 2 (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check4 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 512 p) = packedGen 2 (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check5 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 640 p) = packedGen 2 (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check6 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 768 p) = packedGen 2 (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check7 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 896 p) = packedGen 2 (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check8 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 1024 p) = packedGen 2 (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check9 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 1152 p) = packedGen 2 (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check10 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 1280 p) = packedGen 2 (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check11 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 1408 p) = packedGen 2 (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen2Check12 : ∀ p : Fin 128,
    genMaps 2 (rangeIndex 1600 1536 p) = packedGen 2 (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check0 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 0 p) = packedGen 3 (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check1 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 128 p) = packedGen 3 (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check2 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 256 p) = packedGen 3 (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check3 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 384 p) = packedGen 3 (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check4 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 512 p) = packedGen 3 (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check5 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 640 p) = packedGen 3 (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check6 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 768 p) = packedGen 3 (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check7 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 896 p) = packedGen 3 (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check8 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 1024 p) = packedGen 3 (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check9 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 1152 p) = packedGen 3 (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check10 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 1280 p) = packedGen 3 (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check11 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 1408 p) = packedGen 3 (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem gen3Check12 : ∀ p : Fin 128,
    genMaps 3 (rangeIndex 1600 1536 p) = packedGen 3 (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check0 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 0 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check1 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 128 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check2 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 256 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check3 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 384 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check4 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 512 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check5 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 640 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check6 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 768 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check7 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 896 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check8 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 1024 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check9 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 1152 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check10 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 1280 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check11 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 1408 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep0Check12 : ∀ p : Fin 128,
    repMaps 0 (rangeIndex 1600 1536 p) = ((max4Word 0).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check0 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 0 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check1 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 128 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check2 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 256 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check3 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 384 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check4 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 512 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check5 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 640 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check6 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 768 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check7 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 896 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check8 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 1024 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check9 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 1152 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check10 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 1280 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check11 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 1408 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep1Check12 : ∀ p : Fin 128,
    repMaps 1 (rangeIndex 1600 1536 p) = ((max4Word 1).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check0 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 0 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check1 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 128 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check2 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 256 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check3 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 384 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check4 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 512 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check5 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 640 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check6 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 768 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check7 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 896 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check8 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 1024 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check9 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 1152 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check10 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 1280 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check11 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 1408 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep2Check12 : ∀ p : Fin 128,
    repMaps 2 (rangeIndex 1600 1536 p) = ((max4Word 2).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check0 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 0 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check1 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 128 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check2 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 256 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check3 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 384 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check4 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 512 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check5 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 640 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check6 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 768 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check7 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 896 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check8 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 1024 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check9 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 1152 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check10 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 1280 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check11 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 1408 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep3Check12 : ∀ p : Fin 128,
    repMaps 3 (rangeIndex 1600 1536 p) = ((max4Word 3).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check0 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 0 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check1 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 128 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check2 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 256 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check3 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 384 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check4 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 512 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check5 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 640 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check6 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 768 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check7 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 896 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check8 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 1024 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check9 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 1152 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check10 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 1280 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check11 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 1408 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep4Check12 : ∀ p : Fin 128,
    repMaps 4 (rangeIndex 1600 1536 p) = ((max4Word 4).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check0 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 0 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check1 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 128 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check2 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 256 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check3 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 384 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check4 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 512 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check5 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 640 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check6 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 768 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check7 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 896 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check8 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 1024 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check9 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 1152 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check10 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 1280 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check11 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 1408 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep5Check12 : ∀ p : Fin 128,
    repMaps 5 (rangeIndex 1600 1536 p) = ((max4Word 5).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check0 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 0 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 0 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check1 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 128 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 128 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check2 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 256 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 256 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check3 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 384 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 384 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check4 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 512 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 512 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check5 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 640 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 640 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check6 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 768 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 768 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check7 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 896 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 896 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check8 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 1024 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 1024 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check9 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 1152 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 1152 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check10 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 1280 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 1280 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check11 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 1408 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 1408 p) := by
  apply allFin
  decide +kernel

set_option maxHeartbeats 1600000 in
public theorem rep6Check12 : ∀ p : Fin 128,
    repMaps 6 (rangeIndex 1600 1536 p) = ((max4Word 6).map packedLetter).prod (rangeIndex 1600 1536 p) := by
  apply allFin
  decide +kernel

end Tits.MinimumIndexFiveOvergroups.DoubleCosetCertificate.Max4
