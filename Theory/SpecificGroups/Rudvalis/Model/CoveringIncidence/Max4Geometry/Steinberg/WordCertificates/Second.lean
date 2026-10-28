module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg.CertificateSoundness
import Mathlib.Tactic.FinCases

/-!
# Conjugation by max4 generator 2

All identities are checked in bounded blocks on the original 4060-point model.
Explicit map compositions avoid repeatedly reducing group powers and list products.
Source and original ATLAS attribution: Max4Geometry.Words and SylowOvergroups.
-/

open Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open CatalogueCertificate Max4Normalizers Max4Normalizers.GeneratorMaps
namespace Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
set_option maxRecDepth 30000
set_option Elab.async false

private theorem row0_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 0 = true
  decide +kernel

private theorem row0_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 1 = true
  decide +kernel

private theorem row0_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 2 = true
  decide +kernel

private theorem row0_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 3 = true
  decide +kernel

private theorem row0_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 4 = true
  decide +kernel

private theorem row0_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 5 = true
  decide +kernel

private theorem row0_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 6 = true
  decide +kernel

private theorem row0_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 7 = true
  decide +kernel

private theorem row0_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 8 = true
  decide +kernel

private theorem row0_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 9 = true
  decide +kernel

private theorem row0_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 10 = true
  decide +kernel

private theorem row0_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 11 = true
  decide +kernel

private theorem row0_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 12 = true
  decide +kernel

private theorem row0_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 13 = true
  decide +kernel

private theorem row0_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 14 = true
  decide +kernel

private theorem row0_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 0 * (gen 1)⁻¹) x = (((conjugateWord 1 0).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc4Map (pc5Map (pc11Map (pc12Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (pc12Map (pc13Map (x)))))))))))))))))))))))) 15 = true
  decide +kernel

private theorem row0 : gen 1 * permWord 0 * (gen 1)⁻¹ =
    ((conjugateWord 1 0).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row0_chunk0
  · exact row0_chunk1
  · exact row0_chunk2
  · exact row0_chunk3
  · exact row0_chunk4
  · exact row0_chunk5
  · exact row0_chunk6
  · exact row0_chunk7
  · exact row0_chunk8
  · exact row0_chunk9
  · exact row0_chunk10
  · exact row0_chunk11
  · exact row0_chunk12
  · exact row0_chunk13
  · exact row0_chunk14
  · exact row0_chunk15

private theorem row1_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 0 = true
  decide +kernel

private theorem row1_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 1 = true
  decide +kernel

private theorem row1_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 2 = true
  decide +kernel

private theorem row1_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 3 = true
  decide +kernel

private theorem row1_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 4 = true
  decide +kernel

private theorem row1_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 5 = true
  decide +kernel

private theorem row1_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 6 = true
  decide +kernel

private theorem row1_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 7 = true
  decide +kernel

private theorem row1_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 8 = true
  decide +kernel

private theorem row1_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 9 = true
  decide +kernel

private theorem row1_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 10 = true
  decide +kernel

private theorem row1_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 11 = true
  decide +kernel

private theorem row1_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 12 = true
  decide +kernel

private theorem row1_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 13 = true
  decide +kernel

private theorem row1_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 14 = true
  decide +kernel

private theorem row1_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 1 * (gen 1)⁻¹) x = (((conjugateWord 1 1).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pointMap 3 x)))))))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc8Map (pc9Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc13Map (x)))))))))))))))))) 15 = true
  decide +kernel

private theorem row1 : gen 1 * permWord 1 * (gen 1)⁻¹ =
    ((conjugateWord 1 1).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row1_chunk0
  · exact row1_chunk1
  · exact row1_chunk2
  · exact row1_chunk3
  · exact row1_chunk4
  · exact row1_chunk5
  · exact row1_chunk6
  · exact row1_chunk7
  · exact row1_chunk8
  · exact row1_chunk9
  · exact row1_chunk10
  · exact row1_chunk11
  · exact row1_chunk12
  · exact row1_chunk13
  · exact row1_chunk14
  · exact row1_chunk15

private theorem row2_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 0 = true
  decide +kernel

private theorem row2_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 1 = true
  decide +kernel

private theorem row2_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 2 = true
  decide +kernel

private theorem row2_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 3 = true
  decide +kernel

private theorem row2_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 4 = true
  decide +kernel

private theorem row2_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 5 = true
  decide +kernel

private theorem row2_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 6 = true
  decide +kernel

private theorem row2_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 7 = true
  decide +kernel

private theorem row2_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 8 = true
  decide +kernel

private theorem row2_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 9 = true
  decide +kernel

private theorem row2_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 10 = true
  decide +kernel

private theorem row2_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 11 = true
  decide +kernel

private theorem row2_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 12 = true
  decide +kernel

private theorem row2_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 13 = true
  decide +kernel

private theorem row2_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 14 = true
  decide +kernel

private theorem row2_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 2 * (gen 1)⁻¹) x = (((conjugateWord 1 2).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc8Map (pc9Map (pointMap 3 x))) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))))))))))))))) 15 = true
  decide +kernel

private theorem row2 : gen 1 * permWord 2 * (gen 1)⁻¹ =
    ((conjugateWord 1 2).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row2_chunk0
  · exact row2_chunk1
  · exact row2_chunk2
  · exact row2_chunk3
  · exact row2_chunk4
  · exact row2_chunk5
  · exact row2_chunk6
  · exact row2_chunk7
  · exact row2_chunk8
  · exact row2_chunk9
  · exact row2_chunk10
  · exact row2_chunk11
  · exact row2_chunk12
  · exact row2_chunk13
  · exact row2_chunk14
  · exact row2_chunk15

private theorem row3_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 0 = true
  decide +kernel

private theorem row3_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 1 = true
  decide +kernel

private theorem row3_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 2 = true
  decide +kernel

private theorem row3_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 3 = true
  decide +kernel

private theorem row3_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 4 = true
  decide +kernel

private theorem row3_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 5 = true
  decide +kernel

private theorem row3_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 6 = true
  decide +kernel

private theorem row3_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 7 = true
  decide +kernel

private theorem row3_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 8 = true
  decide +kernel

private theorem row3_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 9 = true
  decide +kernel

private theorem row3_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 10 = true
  decide +kernel

private theorem row3_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 11 = true
  decide +kernel

private theorem row3_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 12 = true
  decide +kernel

private theorem row3_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 13 = true
  decide +kernel

private theorem row3_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 14 = true
  decide +kernel

private theorem row3_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 3 * (gen 1)⁻¹) x = (((conjugateWord 1 3).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x))))))))))) = pc1Map (pc2Map (pc3Map (pc4Map (pc6Map (pc7Map (pc10Map (pc11Map (pc12Map (pc13Map (pc8Map (pc9Map (pc0Map (pc2Map (pc5Map (pc6Map (pc7Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc12Map (pc13Map (x))))))))))))))))))))))))))))))))))))))) 15 = true
  decide +kernel

private theorem row3 : gen 1 * permWord 3 * (gen 1)⁻¹ =
    ((conjugateWord 1 3).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row3_chunk0
  · exact row3_chunk1
  · exact row3_chunk2
  · exact row3_chunk3
  · exact row3_chunk4
  · exact row3_chunk5
  · exact row3_chunk6
  · exact row3_chunk7
  · exact row3_chunk8
  · exact row3_chunk9
  · exact row3_chunk10
  · exact row3_chunk11
  · exact row3_chunk12
  · exact row3_chunk13
  · exact row3_chunk14
  · exact row3_chunk15

private theorem row4_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 0 = true
  decide +kernel

private theorem row4_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 1 = true
  decide +kernel

private theorem row4_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 2 = true
  decide +kernel

private theorem row4_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 3 = true
  decide +kernel

private theorem row4_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 4 = true
  decide +kernel

private theorem row4_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 5 = true
  decide +kernel

private theorem row4_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 6 = true
  decide +kernel

private theorem row4_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 7 = true
  decide +kernel

private theorem row4_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 8 = true
  decide +kernel

private theorem row4_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 9 = true
  decide +kernel

private theorem row4_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 10 = true
  decide +kernel

private theorem row4_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 11 = true
  decide +kernel

private theorem row4_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 12 = true
  decide +kernel

private theorem row4_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 13 = true
  decide +kernel

private theorem row4_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 14 = true
  decide +kernel

private theorem row4_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 4 * (gen 1)⁻¹) x = (((conjugateWord 1 4).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pointMap 3 x)))))))) = pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (pc13Map (x)))))))))) 15 = true
  decide +kernel

private theorem row4 : gen 1 * permWord 4 * (gen 1)⁻¹ =
    ((conjugateWord 1 4).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row4_chunk0
  · exact row4_chunk1
  · exact row4_chunk2
  · exact row4_chunk3
  · exact row4_chunk4
  · exact row4_chunk5
  · exact row4_chunk6
  · exact row4_chunk7
  · exact row4_chunk8
  · exact row4_chunk9
  · exact row4_chunk10
  · exact row4_chunk11
  · exact row4_chunk12
  · exact row4_chunk13
  · exact row4_chunk14
  · exact row4_chunk15

private theorem row5_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 0 = true
  decide +kernel

private theorem row5_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 1 = true
  decide +kernel

private theorem row5_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 2 = true
  decide +kernel

private theorem row5_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 3 = true
  decide +kernel

private theorem row5_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 4 = true
  decide +kernel

private theorem row5_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 5 = true
  decide +kernel

private theorem row5_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 6 = true
  decide +kernel

private theorem row5_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 7 = true
  decide +kernel

private theorem row5_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 8 = true
  decide +kernel

private theorem row5_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 9 = true
  decide +kernel

private theorem row5_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 10 = true
  decide +kernel

private theorem row5_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 11 = true
  decide +kernel

private theorem row5_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 12 = true
  decide +kernel

private theorem row5_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 13 = true
  decide +kernel

private theorem row5_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 14 = true
  decide +kernel

private theorem row5_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 5 * (gen 1)⁻¹) x = (((conjugateWord 1 5).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc11Map (pc12Map (pointMap 3 x))))) = pc6Map (pc13Map (pc12Map (pc13Map (x))))) 15 = true
  decide +kernel

private theorem row5 : gen 1 * permWord 5 * (gen 1)⁻¹ =
    ((conjugateWord 1 5).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row5_chunk0
  · exact row5_chunk1
  · exact row5_chunk2
  · exact row5_chunk3
  · exact row5_chunk4
  · exact row5_chunk5
  · exact row5_chunk6
  · exact row5_chunk7
  · exact row5_chunk8
  · exact row5_chunk9
  · exact row5_chunk10
  · exact row5_chunk11
  · exact row5_chunk12
  · exact row5_chunk13
  · exact row5_chunk14
  · exact row5_chunk15

private theorem row6_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 0 = true
  decide +kernel

private theorem row6_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 1 = true
  decide +kernel

private theorem row6_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 2 = true
  decide +kernel

private theorem row6_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 3 = true
  decide +kernel

private theorem row6_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 4 = true
  decide +kernel

private theorem row6_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 5 = true
  decide +kernel

private theorem row6_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 6 = true
  decide +kernel

private theorem row6_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 7 = true
  decide +kernel

private theorem row6_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 8 = true
  decide +kernel

private theorem row6_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 9 = true
  decide +kernel

private theorem row6_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 10 = true
  decide +kernel

private theorem row6_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 11 = true
  decide +kernel

private theorem row6_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 12 = true
  decide +kernel

private theorem row6_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 13 = true
  decide +kernel

private theorem row6_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 14 = true
  decide +kernel

private theorem row6_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 6 * (gen 1)⁻¹) x = (((conjugateWord 1 6).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pointMap 3 x)))))))) = pc8Map (pc9Map (pc6Map (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (x)))))))))) 15 = true
  decide +kernel

private theorem row6 : gen 1 * permWord 6 * (gen 1)⁻¹ =
    ((conjugateWord 1 6).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row6_chunk0
  · exact row6_chunk1
  · exact row6_chunk2
  · exact row6_chunk3
  · exact row6_chunk4
  · exact row6_chunk5
  · exact row6_chunk6
  · exact row6_chunk7
  · exact row6_chunk8
  · exact row6_chunk9
  · exact row6_chunk10
  · exact row6_chunk11
  · exact row6_chunk12
  · exact row6_chunk13
  · exact row6_chunk14
  · exact row6_chunk15

private theorem row7_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 0 = true
  decide +kernel

private theorem row7_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 1 = true
  decide +kernel

private theorem row7_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 2 = true
  decide +kernel

private theorem row7_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 3 = true
  decide +kernel

private theorem row7_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 4 = true
  decide +kernel

private theorem row7_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 5 = true
  decide +kernel

private theorem row7_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 6 = true
  decide +kernel

private theorem row7_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 7 = true
  decide +kernel

private theorem row7_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 8 = true
  decide +kernel

private theorem row7_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 9 = true
  decide +kernel

private theorem row7_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 10 = true
  decide +kernel

private theorem row7_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 11 = true
  decide +kernel

private theorem row7_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 12 = true
  decide +kernel

private theorem row7_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 13 = true
  decide +kernel

private theorem row7_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 14 = true
  decide +kernel

private theorem row7_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 7 * (gen 1)⁻¹) x = (((conjugateWord 1 7).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pointMap 3 x)) = pc0Map (pc1Map (pc4Map (pc6Map (pc8Map (pc10Map (pc11Map (pc0Map (pc2Map (pc3Map (pc4Map (pc5Map (pc6Map (pc10Map (pc4Map (pc5Map (pc11Map (pc12Map (pc4Map (pc5Map (pc9Map (pc10Map (pc11Map (pc12Map (pc13Map (pc6Map (x))))))))))))))))))))))))))) 15 = true
  decide +kernel

private theorem row7 : gen 1 * permWord 7 * (gen 1)⁻¹ =
    ((conjugateWord 1 7).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row7_chunk0
  · exact row7_chunk1
  · exact row7_chunk2
  · exact row7_chunk3
  · exact row7_chunk4
  · exact row7_chunk5
  · exact row7_chunk6
  · exact row7_chunk7
  · exact row7_chunk8
  · exact row7_chunk9
  · exact row7_chunk10
  · exact row7_chunk11
  · exact row7_chunk12
  · exact row7_chunk13
  · exact row7_chunk14
  · exact row7_chunk15

private theorem row8_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 0 = true
  decide +kernel

private theorem row8_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 1 = true
  decide +kernel

private theorem row8_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 2 = true
  decide +kernel

private theorem row8_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 3 = true
  decide +kernel

private theorem row8_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 4 = true
  decide +kernel

private theorem row8_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 5 = true
  decide +kernel

private theorem row8_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 6 = true
  decide +kernel

private theorem row8_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 7 = true
  decide +kernel

private theorem row8_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 8 = true
  decide +kernel

private theorem row8_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 9 = true
  decide +kernel

private theorem row8_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 10 = true
  decide +kernel

private theorem row8_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 11 = true
  decide +kernel

private theorem row8_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 12 = true
  decide +kernel

private theorem row8_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 13 = true
  decide +kernel

private theorem row8_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 14 = true
  decide +kernel

private theorem row8_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 8 * (gen 1)⁻¹) x = (((conjugateWord 1 8).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pointMap 3 x))))))) = pc13Map (x)) 15 = true
  decide +kernel

private theorem row8 : gen 1 * permWord 8 * (gen 1)⁻¹ =
    ((conjugateWord 1 8).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row8_chunk0
  · exact row8_chunk1
  · exact row8_chunk2
  · exact row8_chunk3
  · exact row8_chunk4
  · exact row8_chunk5
  · exact row8_chunk6
  · exact row8_chunk7
  · exact row8_chunk8
  · exact row8_chunk9
  · exact row8_chunk10
  · exact row8_chunk11
  · exact row8_chunk12
  · exact row8_chunk13
  · exact row8_chunk14
  · exact row8_chunk15

private theorem row9_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 0 = true
  decide +kernel

private theorem row9_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 1 = true
  decide +kernel

private theorem row9_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 2 = true
  decide +kernel

private theorem row9_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 3 = true
  decide +kernel

private theorem row9_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 4 = true
  decide +kernel

private theorem row9_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 5 = true
  decide +kernel

private theorem row9_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 6 = true
  decide +kernel

private theorem row9_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 7 = true
  decide +kernel

private theorem row9_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 8 = true
  decide +kernel

private theorem row9_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 9 = true
  decide +kernel

private theorem row9_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 10 = true
  decide +kernel

private theorem row9_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 11 = true
  decide +kernel

private theorem row9_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 12 = true
  decide +kernel

private theorem row9_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 13 = true
  decide +kernel

private theorem row9_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 14 = true
  decide +kernel

private theorem row9_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 9 * (gen 1)⁻¹) x = (((conjugateWord 1 9).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc13Map (pointMap 3 x)) = pc6Map (pc7Map (pc8Map (pc9Map (pc11Map (pc13Map (pc13Map (x)))))))) 15 = true
  decide +kernel

private theorem row9 : gen 1 * permWord 9 * (gen 1)⁻¹ =
    ((conjugateWord 1 9).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row9_chunk0
  · exact row9_chunk1
  · exact row9_chunk2
  · exact row9_chunk3
  · exact row9_chunk4
  · exact row9_chunk5
  · exact row9_chunk6
  · exact row9_chunk7
  · exact row9_chunk8
  · exact row9_chunk9
  · exact row9_chunk10
  · exact row9_chunk11
  · exact row9_chunk12
  · exact row9_chunk13
  · exact row9_chunk14
  · exact row9_chunk15

private theorem row10_chunk0 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 0 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 0 = true
  decide +kernel

private theorem row10_chunk1 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 1 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 1 = true
  decide +kernel

private theorem row10_chunk2 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 2 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 2 = true
  decide +kernel

private theorem row10_chunk3 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 3 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 3 = true
  decide +kernel

private theorem row10_chunk4 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 4 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 4 = true
  decide +kernel

private theorem row10_chunk5 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 5 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 5 = true
  decide +kernel

private theorem row10_chunk6 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 6 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 6 = true
  decide +kernel

private theorem row10_chunk7 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 7 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 7 = true
  decide +kernel

private theorem row10_chunk8 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 8 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 8 = true
  decide +kernel

private theorem row10_chunk9 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 9 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 9 = true
  decide +kernel

private theorem row10_chunk10 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 10 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 10 = true
  decide +kernel

private theorem row10_chunk11 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 11 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 11 = true
  decide +kernel

private theorem row10_chunk12 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 12 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 12 = true
  decide +kernel

private theorem row10_chunk13 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 13 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 13 = true
  decide +kernel

private theorem row10_chunk14 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 14 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 14 = true
  decide +kernel

private theorem row10_chunk15 :
    checkChunk (fun x => (gen 1 * permWord 10 * (gen 1)⁻¹) x = (((conjugateWord 1 10).map permWord).prod) x) 15 = true := by
  change checkChunk (fun x => pointMap 1 (pc12Map (pc13Map (pointMap 3 x))) = pc13Map (pc12Map (pc13Map (x)))) 15 = true
  decide +kernel

private theorem row10 : gen 1 * permWord 10 * (gen 1)⁻¹ =
    ((conjugateWord 1 10).map permWord).prod := by
  apply Equiv.ext
  apply allFinChunks
  intro b
  fin_cases b
  · exact row10_chunk0
  · exact row10_chunk1
  · exact row10_chunk2
  · exact row10_chunk3
  · exact row10_chunk4
  · exact row10_chunk5
  · exact row10_chunk6
  · exact row10_chunk7
  · exact row10_chunk8
  · exact row10_chunk9
  · exact row10_chunk10
  · exact row10_chunk11
  · exact row10_chunk12
  · exact row10_chunk13
  · exact row10_chunk14
  · exact row10_chunk15

public theorem second_words (j : Fin 11) :
    (actorGenerator 1 : Model) * Max4Words.generator j * (actorGenerator 1 : Model)⁻¹ =
      ((conjugateWord 1 j).map Max4Words.generator).prod := by
  fin_cases j
  · exact transfer 1 0 row0
  · exact transfer 1 1 row1
  · exact transfer 1 2 row2
  · exact transfer 1 3 row3
  · exact transfer 1 4 row4
  · exact transfer 1 5 row5
  · exact transfer 1 6 row6
  · exact transfer 1 7 row7
  · exact transfer 1 8 row8
  · exact transfer 1 9 row9
  · exact transfer 1 10 row10

end Rudvalis.CoveringIncidence.Max4Steinberg.WordCertificates
