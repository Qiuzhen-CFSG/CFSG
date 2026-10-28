module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.SubgroupActions.Segment04

/-!
# Kernel certificate for segment05_correct

Each bounded check compares 896 consecutive point images. The soundness
lemma covers every point and composes the already certified segment walks.
Checks elaborate sequentially to bound the memory used by kernel reduction.
Source: the unchanged Presentation/source/discovery/ files, via
SubgroupActions/source/generate.py. Data attribution and licensing remain in
Presentation/source/README.md. All numerical equalities use kernel reduction.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.SubgroupActionCertificate

set_option Elab.async false

set_option maxRecDepth 2048 in
private theorem block00 : checkBlocks segment05 [actionATree, actionBTree] 0 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block01 : checkBlocks segment05 [actionATree, actionBTree] 7 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block02 : checkBlocks segment05 [actionATree, actionBTree] 14 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block03 : checkBlocks segment05 [actionATree, actionBTree] 21 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block04 : checkBlocks segment05 [actionATree, actionBTree] 28 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block05 : checkBlocks segment05 [actionATree, actionBTree] 35 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block06 : checkBlocks segment05 [actionATree, actionBTree] 42 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block07 : checkBlocks segment05 [actionATree, actionBTree] 49 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block08 : checkBlocks segment05 [actionATree, actionBTree] 56 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block09 : checkBlocks segment05 [actionATree, actionBTree] 63 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block10 : checkBlocks segment05 [actionATree, actionBTree] 70 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block11 : checkBlocks segment05 [actionATree, actionBTree] 77 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block12 : checkBlocks segment05 [actionATree, actionBTree] 84 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block13 : checkBlocks segment05 [actionATree, actionBTree] 91 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block14 : checkBlocks segment05 [actionATree, actionBTree] 98 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block15 : checkBlocks segment05 [actionATree, actionBTree] 105 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block16 : checkBlocks segment05 [actionATree, actionBTree] 112 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block17 : checkBlocks segment05 [actionATree, actionBTree] 119 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block18 : checkBlocks segment05 [actionATree, actionBTree] 126 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block19 : checkBlocks segment05 [actionATree, actionBTree] 133 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block20 : checkBlocks segment05 [actionATree, actionBTree] 140 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block21 : checkBlocks segment05 [actionATree, actionBTree] 147 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block22 : checkBlocks segment05 [actionATree, actionBTree] 154 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block23 : checkBlocks segment05 [actionATree, actionBTree] 161 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block24 : checkBlocks segment05 [actionATree, actionBTree] 168 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block25 : checkBlocks segment05 [actionATree, actionBTree] 175 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block26 : checkBlocks segment05 [actionATree, actionBTree] 182 7 = true := by
  decide +kernel

theorem segment05_correct : Represents segment05 word05 := by
  refine represents_of_checks segment05 [(actionATree, [0]), (actionBTree, [1])] ?_ 7 27 (by decide) ?_
  · intro t w h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact actionA_represents
    · exact actionB_represents
  · intro q
    fin_cases q
    · exact block00
    · exact block01
    · exact block02
    · exact block03
    · exact block04
    · exact block05
    · exact block06
    · exact block07
    · exact block08
    · exact block09
    · exact block10
    · exact block11
    · exact block12
    · exact block13
    · exact block14
    · exact block15
    · exact block16
    · exact block17
    · exact block18
    · exact block19
    · exact block20
    · exact block21
    · exact block22
    · exact block23
    · exact block24
    · exact block25
    · exact block26

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.SubgroupActionCertificate
