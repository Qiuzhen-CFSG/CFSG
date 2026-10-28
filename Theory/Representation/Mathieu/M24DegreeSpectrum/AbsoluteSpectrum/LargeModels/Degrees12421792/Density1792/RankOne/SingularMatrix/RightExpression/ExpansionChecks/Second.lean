module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.ExpansionChecks.SecondData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideSecond
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# Complete expansion certificate for the second ATLAS generator

Each bounded block certifies its full balanced radix conversion by kernel
reduction. The proved conversion theorem recovers the original digit checker;
`spread_step` and `spread_append` cover every row and all 1792 digits.
The original untransposed ATLAS array and the wide table are unchanged.
See `source/README.md` for attribution, soundness and measurements.
-/

set_option Elab.async false

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate
open ExpansionChecks

set_option maxRecDepth 8192 in
private theorem second_tree_0000 :
    (wideSecond0000.drop 0).take 32 =
      ((second0000.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0032 :
    (wideSecond0000.drop 32).take 32 =
      ((second0000.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0064 :
    (wideSecond0000.drop 64).take 32 =
      ((second0000.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0096 :
    (wideSecond0000.drop 96).take 32 =
      ((second0000.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0000 :
    Wide.checkSpreadRows 1792 second0000 wideSecond0000 = true := by
  change Wide.checkSpreadRows 1792 (second0000.drop 0) (wideSecond0000.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0000)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0032)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0064)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0096)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0128 :
    (wideSecond0128.drop 0).take 32 =
      ((second0128.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0160 :
    (wideSecond0128.drop 32).take 32 =
      ((second0128.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0192 :
    (wideSecond0128.drop 64).take 32 =
      ((second0128.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0224 :
    (wideSecond0128.drop 96).take 32 =
      ((second0128.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0128 :
    Wide.checkSpreadRows 1792 second0128 wideSecond0128 = true := by
  change Wide.checkSpreadRows 1792 (second0128.drop 0) (wideSecond0128.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0128)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0160)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0192)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0224)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0256 :
    (wideSecond0256.drop 0).take 32 =
      ((second0256.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0288 :
    (wideSecond0256.drop 32).take 32 =
      ((second0256.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0320 :
    (wideSecond0256.drop 64).take 32 =
      ((second0256.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0352 :
    (wideSecond0256.drop 96).take 32 =
      ((second0256.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0256 :
    Wide.checkSpreadRows 1792 second0256 wideSecond0256 = true := by
  change Wide.checkSpreadRows 1792 (second0256.drop 0) (wideSecond0256.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0256)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0288)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0320)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0352)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0384 :
    (wideSecond0384.drop 0).take 32 =
      ((second0384.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0416 :
    (wideSecond0384.drop 32).take 32 =
      ((second0384.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0448 :
    (wideSecond0384.drop 64).take 32 =
      ((second0384.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0480 :
    (wideSecond0384.drop 96).take 32 =
      ((second0384.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0384 :
    Wide.checkSpreadRows 1792 second0384 wideSecond0384 = true := by
  change Wide.checkSpreadRows 1792 (second0384.drop 0) (wideSecond0384.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0384)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0416)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0448)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0480)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0512 :
    (wideSecond0512.drop 0).take 32 =
      ((second0512.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0544 :
    (wideSecond0512.drop 32).take 32 =
      ((second0512.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0576 :
    (wideSecond0512.drop 64).take 32 =
      ((second0512.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0608 :
    (wideSecond0512.drop 96).take 32 =
      ((second0512.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0512 :
    Wide.checkSpreadRows 1792 second0512 wideSecond0512 = true := by
  change Wide.checkSpreadRows 1792 (second0512.drop 0) (wideSecond0512.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0512)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0544)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0576)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0608)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0640 :
    (wideSecond0640.drop 0).take 32 =
      ((second0640.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0672 :
    (wideSecond0640.drop 32).take 32 =
      ((second0640.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0704 :
    (wideSecond0640.drop 64).take 32 =
      ((second0640.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0736 :
    (wideSecond0640.drop 96).take 32 =
      ((second0640.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0640 :
    Wide.checkSpreadRows 1792 second0640 wideSecond0640 = true := by
  change Wide.checkSpreadRows 1792 (second0640.drop 0) (wideSecond0640.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0640)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0672)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0704)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0736)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0768 :
    (wideSecond0768.drop 0).take 32 =
      ((second0768.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0800 :
    (wideSecond0768.drop 32).take 32 =
      ((second0768.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0832 :
    (wideSecond0768.drop 64).take 32 =
      ((second0768.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0864 :
    (wideSecond0768.drop 96).take 32 =
      ((second0768.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0768 :
    Wide.checkSpreadRows 1792 second0768 wideSecond0768 = true := by
  change Wide.checkSpreadRows 1792 (second0768.drop 0) (wideSecond0768.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0768)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0800)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0832)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0864)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0896 :
    (wideSecond0896.drop 0).take 32 =
      ((second0896.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0928 :
    (wideSecond0896.drop 32).take 32 =
      ((second0896.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0960 :
    (wideSecond0896.drop 64).take 32 =
      ((second0896.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_0992 :
    (wideSecond0896.drop 96).take 32 =
      ((second0896.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_0896 :
    Wide.checkSpreadRows 1792 second0896 wideSecond0896 = true := by
  change Wide.checkSpreadRows 1792 (second0896.drop 0) (wideSecond0896.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0896)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0928)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0960)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_0992)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1024 :
    (wideSecond1024.drop 0).take 32 =
      ((second1024.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1056 :
    (wideSecond1024.drop 32).take 32 =
      ((second1024.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1088 :
    (wideSecond1024.drop 64).take 32 =
      ((second1024.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1120 :
    (wideSecond1024.drop 96).take 32 =
      ((second1024.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_1024 :
    Wide.checkSpreadRows 1792 second1024 wideSecond1024 = true := by
  change Wide.checkSpreadRows 1792 (second1024.drop 0) (wideSecond1024.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1024)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1056)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1088)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1120)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1152 :
    (wideSecond1152.drop 0).take 32 =
      ((second1152.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1184 :
    (wideSecond1152.drop 32).take 32 =
      ((second1152.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1216 :
    (wideSecond1152.drop 64).take 32 =
      ((second1152.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1248 :
    (wideSecond1152.drop 96).take 32 =
      ((second1152.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_1152 :
    Wide.checkSpreadRows 1792 second1152 wideSecond1152 = true := by
  change Wide.checkSpreadRows 1792 (second1152.drop 0) (wideSecond1152.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1152)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1184)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1216)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1248)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1280 :
    (wideSecond1280.drop 0).take 32 =
      ((second1280.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1312 :
    (wideSecond1280.drop 32).take 32 =
      ((second1280.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1344 :
    (wideSecond1280.drop 64).take 32 =
      ((second1280.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1376 :
    (wideSecond1280.drop 96).take 32 =
      ((second1280.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_1280 :
    Wide.checkSpreadRows 1792 second1280 wideSecond1280 = true := by
  change Wide.checkSpreadRows 1792 (second1280.drop 0) (wideSecond1280.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1280)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1312)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1344)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1376)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1408 :
    (wideSecond1408.drop 0).take 32 =
      ((second1408.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1440 :
    (wideSecond1408.drop 32).take 32 =
      ((second1408.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1472 :
    (wideSecond1408.drop 64).take 32 =
      ((second1408.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1504 :
    (wideSecond1408.drop 96).take 32 =
      ((second1408.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_1408 :
    Wide.checkSpreadRows 1792 second1408 wideSecond1408 = true := by
  change Wide.checkSpreadRows 1792 (second1408.drop 0) (wideSecond1408.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1408)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1440)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1472)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1504)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1536 :
    (wideSecond1536.drop 0).take 32 =
      ((second1536.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1568 :
    (wideSecond1536.drop 32).take 32 =
      ((second1536.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1600 :
    (wideSecond1536.drop 64).take 32 =
      ((second1536.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1632 :
    (wideSecond1536.drop 96).take 32 =
      ((second1536.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_1536 :
    Wide.checkSpreadRows 1792 second1536 wideSecond1536 = true := by
  change Wide.checkSpreadRows 1792 (second1536.drop 0) (wideSecond1536.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1536)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1568)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1600)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1632)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1664 :
    (wideSecond1664.drop 0).take 32 =
      ((second1664.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1696 :
    (wideSecond1664.drop 32).take 32 =
      ((second1664.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1728 :
    (wideSecond1664.drop 64).take 32 =
      ((second1664.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_tree_1760 :
    (wideSecond1664.drop 96).take 32 =
      ((second1664.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_block_1664 :
    Wide.checkSpreadRows 1792 second1664 wideSecond1664 = true := by
  change Wide.checkSpreadRows 1792 (second1664.drop 0) (wideSecond1664.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1664)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1696)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1728)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ second_tree_1760)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem second_original_rows :
    Data1792.secondRows.toList =
      second0000 ++ second0128 ++ second0256 ++ second0384 ++ second0512 ++ second0640 ++ second0768 ++ second0896 ++ second1024 ++ second1152 ++ second1280 ++ second1408 ++ second1536 ++ second1664 := by
  decide +kernel

/-- Every expanded digit of every original second-generator row is checked. -/
theorem second_expanded_checked :
    Wide.checkSpreadRows 1792 Data1792.secondRows.toList wideSecond = true := by
  rw [second_original_rows]
  unfold wideSecond
  apply spread_append _ _ _ _ second_block_0000
  apply spread_append _ _ _ _ second_block_0128
  apply spread_append _ _ _ _ second_block_0256
  apply spread_append _ _ _ _ second_block_0384
  apply spread_append _ _ _ _ second_block_0512
  apply spread_append _ _ _ _ second_block_0640
  apply spread_append _ _ _ _ second_block_0768
  apply spread_append _ _ _ _ second_block_0896
  apply spread_append _ _ _ _ second_block_1024
  apply spread_append _ _ _ _ second_block_1152
  apply spread_append _ _ _ _ second_block_1280
  apply spread_append _ _ _ _ second_block_1408
  apply spread_append _ _ _ _ second_block_1536
  exact second_block_1664

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate
