module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.SubgroupActions.Segment12

/-!
# Kernel certificate for right_correct_normalized

Each bounded check compares 384 consecutive point images. The soundness
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
private theorem block00 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 0 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block01 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 3 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block02 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 6 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block03 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 9 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block04 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 12 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block05 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 15 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block06 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 18 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block07 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 21 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block08 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 24 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block09 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 27 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block10 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 30 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block11 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 33 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block12 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 36 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block13 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 39 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block14 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 42 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block15 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 45 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block16 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 48 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block17 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 51 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block18 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 54 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block19 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 57 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block20 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 60 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block21 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 63 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block22 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 66 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block23 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 69 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block24 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 72 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block25 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 75 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block26 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 78 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block27 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 81 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block28 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 84 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block29 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 87 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block30 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 90 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block31 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 93 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block32 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 96 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block33 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 99 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block34 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 102 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block35 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 105 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block36 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 108 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block37 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 111 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block38 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 114 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block39 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 117 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block40 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 120 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block41 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 123 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block42 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 126 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block43 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 129 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block44 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 132 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block45 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 135 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block46 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 138 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block47 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 141 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block48 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 144 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block49 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 147 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block50 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 150 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block51 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 153 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block52 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 156 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block53 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 159 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block54 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 162 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block55 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 165 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block56 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 168 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block57 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 171 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block58 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 174 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block59 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 177 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block60 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 180 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block61 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 183 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block62 : checkBlocks rightTree [actionBTree, segment04, segment09, segment10, actionBTree, segment11, segment05, segment07, segment08, segment07, segment12] 186 3 = true := by
  decide +kernel

theorem right_correct_normalized : Represents rightTree (rightWord.map normalizeLetter) := by
  refine represents_of_checks rightTree [(actionBTree, [1]), (segment04, word04), (segment09, word09), (segment10, word10), (actionBTree, [1]), (segment11, word11), (segment05, word05), (segment07, word07), (segment08, word08), (segment07, word07), (segment12, word12)] ?_ 3 63 (by decide) ?_
  · intro t w h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact actionB_represents
    · exact segment04_correct
    · exact segment09_correct
    · exact segment10_correct
    · exact actionB_represents
    · exact segment11_correct
    · exact segment05_correct
    · exact segment07_correct
    · exact segment08_correct
    · exact segment07_correct
    · exact segment12_correct
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
    · exact block27
    · exact block28
    · exact block29
    · exact block30
    · exact block31
    · exact block32
    · exact block33
    · exact block34
    · exact block35
    · exact block36
    · exact block37
    · exact block38
    · exact block39
    · exact block40
    · exact block41
    · exact block42
    · exact block43
    · exact block44
    · exact block45
    · exact block46
    · exact block47
    · exact block48
    · exact block49
    · exact block50
    · exact block51
    · exact block52
    · exact block53
    · exact block54
    · exact block55
    · exact block56
    · exact block57
    · exact block58
    · exact block59
    · exact block60
    · exact block61
    · exact block62

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients.SubgroupActionCertificate
