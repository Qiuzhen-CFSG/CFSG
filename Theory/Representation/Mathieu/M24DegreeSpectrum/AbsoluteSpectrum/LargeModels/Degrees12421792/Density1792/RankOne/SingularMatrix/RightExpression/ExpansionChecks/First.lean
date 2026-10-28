module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.ExpansionChecks.FirstData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.RightExpression.WideFirst
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# Complete expansion certificate for the first ATLAS generator

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
private theorem first_tree_0000 :
    (wideFirst0000.drop 0).take 32 =
      ((first0000.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0032 :
    (wideFirst0000.drop 32).take 32 =
      ((first0000.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0064 :
    (wideFirst0000.drop 64).take 32 =
      ((first0000.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0096 :
    (wideFirst0000.drop 96).take 32 =
      ((first0000.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0000 :
    Wide.checkSpreadRows 1792 first0000 wideFirst0000 = true := by
  change Wide.checkSpreadRows 1792 (first0000.drop 0) (wideFirst0000.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0000)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0032)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0064)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0096)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0128 :
    (wideFirst0128.drop 0).take 32 =
      ((first0128.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0160 :
    (wideFirst0128.drop 32).take 32 =
      ((first0128.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0192 :
    (wideFirst0128.drop 64).take 32 =
      ((first0128.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0224 :
    (wideFirst0128.drop 96).take 32 =
      ((first0128.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0128 :
    Wide.checkSpreadRows 1792 first0128 wideFirst0128 = true := by
  change Wide.checkSpreadRows 1792 (first0128.drop 0) (wideFirst0128.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0128)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0160)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0192)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0224)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0256 :
    (wideFirst0256.drop 0).take 32 =
      ((first0256.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0288 :
    (wideFirst0256.drop 32).take 32 =
      ((first0256.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0320 :
    (wideFirst0256.drop 64).take 32 =
      ((first0256.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0352 :
    (wideFirst0256.drop 96).take 32 =
      ((first0256.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0256 :
    Wide.checkSpreadRows 1792 first0256 wideFirst0256 = true := by
  change Wide.checkSpreadRows 1792 (first0256.drop 0) (wideFirst0256.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0256)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0288)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0320)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0352)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0384 :
    (wideFirst0384.drop 0).take 32 =
      ((first0384.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0416 :
    (wideFirst0384.drop 32).take 32 =
      ((first0384.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0448 :
    (wideFirst0384.drop 64).take 32 =
      ((first0384.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0480 :
    (wideFirst0384.drop 96).take 32 =
      ((first0384.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0384 :
    Wide.checkSpreadRows 1792 first0384 wideFirst0384 = true := by
  change Wide.checkSpreadRows 1792 (first0384.drop 0) (wideFirst0384.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0384)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0416)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0448)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0480)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0512 :
    (wideFirst0512.drop 0).take 32 =
      ((first0512.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0544 :
    (wideFirst0512.drop 32).take 32 =
      ((first0512.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0576 :
    (wideFirst0512.drop 64).take 32 =
      ((first0512.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0608 :
    (wideFirst0512.drop 96).take 32 =
      ((first0512.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0512 :
    Wide.checkSpreadRows 1792 first0512 wideFirst0512 = true := by
  change Wide.checkSpreadRows 1792 (first0512.drop 0) (wideFirst0512.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0512)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0544)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0576)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0608)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0640 :
    (wideFirst0640.drop 0).take 32 =
      ((first0640.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0672 :
    (wideFirst0640.drop 32).take 32 =
      ((first0640.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0704 :
    (wideFirst0640.drop 64).take 32 =
      ((first0640.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0736 :
    (wideFirst0640.drop 96).take 32 =
      ((first0640.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0640 :
    Wide.checkSpreadRows 1792 first0640 wideFirst0640 = true := by
  change Wide.checkSpreadRows 1792 (first0640.drop 0) (wideFirst0640.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0640)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0672)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0704)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0736)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0768 :
    (wideFirst0768.drop 0).take 32 =
      ((first0768.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0800 :
    (wideFirst0768.drop 32).take 32 =
      ((first0768.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0832 :
    (wideFirst0768.drop 64).take 32 =
      ((first0768.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0864 :
    (wideFirst0768.drop 96).take 32 =
      ((first0768.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0768 :
    Wide.checkSpreadRows 1792 first0768 wideFirst0768 = true := by
  change Wide.checkSpreadRows 1792 (first0768.drop 0) (wideFirst0768.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0768)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0800)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0832)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0864)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0896 :
    (wideFirst0896.drop 0).take 32 =
      ((first0896.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0928 :
    (wideFirst0896.drop 32).take 32 =
      ((first0896.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0960 :
    (wideFirst0896.drop 64).take 32 =
      ((first0896.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_0992 :
    (wideFirst0896.drop 96).take 32 =
      ((first0896.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_0896 :
    Wide.checkSpreadRows 1792 first0896 wideFirst0896 = true := by
  change Wide.checkSpreadRows 1792 (first0896.drop 0) (wideFirst0896.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0896)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0928)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0960)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_0992)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1024 :
    (wideFirst1024.drop 0).take 32 =
      ((first1024.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1056 :
    (wideFirst1024.drop 32).take 32 =
      ((first1024.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1088 :
    (wideFirst1024.drop 64).take 32 =
      ((first1024.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1120 :
    (wideFirst1024.drop 96).take 32 =
      ((first1024.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_1024 :
    Wide.checkSpreadRows 1792 first1024 wideFirst1024 = true := by
  change Wide.checkSpreadRows 1792 (first1024.drop 0) (wideFirst1024.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1024)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1056)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1088)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1120)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1152 :
    (wideFirst1152.drop 0).take 32 =
      ((first1152.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1184 :
    (wideFirst1152.drop 32).take 32 =
      ((first1152.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1216 :
    (wideFirst1152.drop 64).take 32 =
      ((first1152.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1248 :
    (wideFirst1152.drop 96).take 32 =
      ((first1152.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_1152 :
    Wide.checkSpreadRows 1792 first1152 wideFirst1152 = true := by
  change Wide.checkSpreadRows 1792 (first1152.drop 0) (wideFirst1152.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1152)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1184)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1216)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1248)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1280 :
    (wideFirst1280.drop 0).take 32 =
      ((first1280.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1312 :
    (wideFirst1280.drop 32).take 32 =
      ((first1280.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1344 :
    (wideFirst1280.drop 64).take 32 =
      ((first1280.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1376 :
    (wideFirst1280.drop 96).take 32 =
      ((first1280.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_1280 :
    Wide.checkSpreadRows 1792 first1280 wideFirst1280 = true := by
  change Wide.checkSpreadRows 1792 (first1280.drop 0) (wideFirst1280.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1280)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1312)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1344)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1376)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1408 :
    (wideFirst1408.drop 0).take 32 =
      ((first1408.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1440 :
    (wideFirst1408.drop 32).take 32 =
      ((first1408.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1472 :
    (wideFirst1408.drop 64).take 32 =
      ((first1408.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1504 :
    (wideFirst1408.drop 96).take 32 =
      ((first1408.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_1408 :
    Wide.checkSpreadRows 1792 first1408 wideFirst1408 = true := by
  change Wide.checkSpreadRows 1792 (first1408.drop 0) (wideFirst1408.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1408)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1440)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1472)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1504)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1536 :
    (wideFirst1536.drop 0).take 32 =
      ((first1536.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1568 :
    (wideFirst1536.drop 32).take 32 =
      ((first1536.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1600 :
    (wideFirst1536.drop 64).take 32 =
      ((first1536.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1632 :
    (wideFirst1536.drop 96).take 32 =
      ((first1536.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_1536 :
    Wide.checkSpreadRows 1792 first1536 wideFirst1536 = true := by
  change Wide.checkSpreadRows 1792 (first1536.drop 0) (wideFirst1536.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1536)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1568)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1600)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1632)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1664 :
    (wideFirst1664.drop 0).take 32 =
      ((first1664.drop 0).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1696 :
    (wideFirst1664.drop 32).take 32 =
      ((first1664.drop 32).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1728 :
    (wideFirst1664.drop 64).take 32 =
      ((first1664.drop 64).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_tree_1760 :
    (wideFirst1664.drop 96).take 32 =
      ((first1664.drop 96).take 32).map (expandTree 6 1792) := by
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_block_1664 :
    Wide.checkSpreadRows 1792 first1664 wideFirst1664 = true := by
  change Wide.checkSpreadRows 1792 (first1664.drop 0) (wideFirst1664.drop 0) = true
  apply spread_step _ _ 0 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1664)
  apply spread_step _ _ 32 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1696)
  apply spread_step _ _ 64 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1728)
  apply spread_step _ _ 96 32
    (checkSpreadRows_of_tree 6 1792 _ _ first_tree_1760)
  decide +kernel

set_option maxRecDepth 8192 in
private theorem first_original_rows :
    Data1792.firstRows.toList =
      first0000 ++ first0128 ++ first0256 ++ first0384 ++ first0512 ++ first0640 ++ first0768 ++ first0896 ++ first1024 ++ first1152 ++ first1280 ++ first1408 ++ first1536 ++ first1664 := by
  decide +kernel

/-- Every expanded digit of every original first-generator row is checked. -/
theorem first_expanded_checked :
    Wide.checkSpreadRows 1792 Data1792.firstRows.toList wideFirst = true := by
  rw [first_original_rows]
  unfold wideFirst
  apply spread_append _ _ _ _ first_block_0000
  apply spread_append _ _ _ _ first_block_0128
  apply spread_append _ _ _ _ first_block_0256
  apply spread_append _ _ _ _ first_block_0384
  apply spread_append _ _ _ _ first_block_0512
  apply spread_append _ _ _ _ first_block_0640
  apply spread_append _ _ _ _ first_block_0768
  apply spread_append _ _ _ _ first_block_0896
  apply spread_append _ _ _ _ first_block_1024
  apply spread_append _ _ _ _ first_block_1152
  apply spread_append _ _ _ _ first_block_1280
  apply spread_append _ _ _ _ first_block_1408
  apply spread_append _ _ _ _ first_block_1536
  exact first_block_1664

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.RightCertificate
