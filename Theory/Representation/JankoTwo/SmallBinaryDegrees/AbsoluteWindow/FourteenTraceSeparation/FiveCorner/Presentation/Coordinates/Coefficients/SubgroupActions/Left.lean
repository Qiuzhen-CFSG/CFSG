module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.SubgroupActions.Segment12

/-!
# Kernel certificate for left_correct_normalized

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
private theorem block00 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 0 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block01 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 3 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block02 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 6 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block03 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 9 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block04 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 12 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block05 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 15 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block06 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 18 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block07 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 21 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block08 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 24 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block09 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 27 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block10 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 30 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block11 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 33 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block12 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 36 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block13 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 39 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block14 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 42 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block15 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 45 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block16 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 48 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block17 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 51 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block18 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 54 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block19 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 57 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block20 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 60 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block21 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 63 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block22 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 66 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block23 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 69 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block24 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 72 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block25 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 75 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block26 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 78 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block27 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 81 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block28 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 84 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block29 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 87 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block30 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 90 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block31 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 93 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block32 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 96 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block33 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 99 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block34 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 102 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block35 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 105 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block36 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 108 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block37 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 111 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block38 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 114 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block39 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 117 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block40 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 120 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block41 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 123 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block42 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 126 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block43 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 129 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block44 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 132 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block45 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 135 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block46 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 138 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block47 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 141 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block48 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 144 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block49 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 147 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block50 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 150 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block51 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 153 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block52 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 156 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block53 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 159 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block54 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 162 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block55 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 165 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block56 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 168 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block57 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 171 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block58 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 174 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block59 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 177 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block60 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 180 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block61 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 183 3 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block62 : checkBlocks leftTree [segment07, segment07, segment11, segment10, segment07, segment10, segment12, actionATree] 186 3 = true := by
  decide +kernel

theorem left_correct_normalized : Represents leftTree (leftWord.map normalizeLetter) := by
  refine represents_of_checks leftTree [(segment07, word07), (segment07, word07), (segment11, word11), (segment10, word10), (segment07, word07), (segment10, word10), (segment12, word12), (actionATree, [0])] ?_ 3 63 (by decide) ?_
  · intro t w h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact segment07_correct
    · exact segment07_correct
    · exact segment11_correct
    · exact segment10_correct
    · exact segment07_correct
    · exact segment10_correct
    · exact segment12_correct
    · exact actionA_represents
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
