module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows00
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows01
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows02
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows03
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows04
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows05
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows06
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows07
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows08
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows09
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows10
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows11
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows12
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows13
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows14
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows15
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows16
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows17
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows18
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows19
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows20
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.ActionTable.Rows21

/-!
# Complete Fi22 root-action table in the published quadratic coordinates

Every ordered pair fixed by the literal ATLAS generator A satisfies the unitary
transvection formula, up to a nonzero scalar in the published quadratic field.
The certificate includes the zero-vector label 1982 in both positions.

The proof combines all checked rows, uses the certified enumeration of the fixed
labels, and translates packed arithmetic to the original field formula. The
word evaluator is definitionally the one in `Generation.Evaluation`, whose
`rootAction_eq` identifies it with the actual conjugate in the shared carrier.
There is no centralizing, generation, or action-comparison premise.

This supplies the remaining numerical input to the parent labeling assembly
for the 2A centralizer in GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. ATLAS F22G1-p3510B0 attribution and the
left-action convention are recorded in `AtlasCarriers/source/README.md`.
-/

public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
open KernelCertificate ActionTable

private theorem all_rows (i : Fin 694) :
    BitNetwork.check (rowCheck (label i.val)) 0 3510 = true := by
  by_cases h0 : i.val < 32
  · exact rows00 i (by omega) h0
  by_cases h1 : i.val < 64
  · exact rows01 i (by omega) h1
  by_cases h2 : i.val < 96
  · exact rows02 i (by omega) h2
  by_cases h3 : i.val < 128
  · exact rows03 i (by omega) h3
  by_cases h4 : i.val < 160
  · exact rows04 i (by omega) h4
  by_cases h5 : i.val < 192
  · exact rows05 i (by omega) h5
  by_cases h6 : i.val < 224
  · exact rows06 i (by omega) h6
  by_cases h7 : i.val < 256
  · exact rows07 i (by omega) h7
  by_cases h8 : i.val < 288
  · exact rows08 i (by omega) h8
  by_cases h9 : i.val < 320
  · exact rows09 i (by omega) h9
  by_cases h10 : i.val < 352
  · exact rows10 i (by omega) h10
  by_cases h11 : i.val < 384
  · exact rows11 i (by omega) h11
  by_cases h12 : i.val < 416
  · exact rows12 i (by omega) h12
  by_cases h13 : i.val < 448
  · exact rows13 i (by omega) h13
  by_cases h14 : i.val < 480
  · exact rows14 i (by omega) h14
  by_cases h15 : i.val < 512
  · exact rows15 i (by omega) h15
  by_cases h16 : i.val < 544
  · exact rows16 i (by omega) h16
  by_cases h17 : i.val < 576
  · exact rows17 i (by omega) h17
  by_cases h18 : i.val < 608
  · exact rows18 i (by omega) h18
  by_cases h19 : i.val < 640
  · exact rows19 i (by omega) h19
  by_cases h20 : i.val < 672
  · exact rows20 i (by omega) h20
  exact rows21 i (by omega) i.isLt

/-- Complete numerical action certificate, including the distinguished singleton. -/
theorem coordinate_actions (x y : Fin 3510)
    (hx : fastA x = x) (hy : fastA y = y) :
    ∃ c : Four, c ≠ 0 ∧ c • representative (Generation.rootAction x y) =
      transvection (representative x) (representative y) := by
  have h := all_rows (labelIndex x)
  rw [label_labelIndex x hx] at h
  exact rowCheck_sound x h y hy

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
