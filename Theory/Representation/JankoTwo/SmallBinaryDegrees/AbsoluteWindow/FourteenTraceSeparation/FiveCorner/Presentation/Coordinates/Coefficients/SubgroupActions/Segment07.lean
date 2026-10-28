module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.SubgroupActions.Segment06

/-!
# Kernel certificate for segment07_correct

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
private theorem block00 : checkBlocks segment07 [segment06, segment06] 0 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block01 : checkBlocks segment07 [segment06, segment06] 7 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block02 : checkBlocks segment07 [segment06, segment06] 14 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block03 : checkBlocks segment07 [segment06, segment06] 21 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block04 : checkBlocks segment07 [segment06, segment06] 28 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block05 : checkBlocks segment07 [segment06, segment06] 35 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block06 : checkBlocks segment07 [segment06, segment06] 42 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block07 : checkBlocks segment07 [segment06, segment06] 49 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block08 : checkBlocks segment07 [segment06, segment06] 56 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block09 : checkBlocks segment07 [segment06, segment06] 63 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block10 : checkBlocks segment07 [segment06, segment06] 70 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block11 : checkBlocks segment07 [segment06, segment06] 77 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block12 : checkBlocks segment07 [segment06, segment06] 84 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block13 : checkBlocks segment07 [segment06, segment06] 91 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block14 : checkBlocks segment07 [segment06, segment06] 98 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block15 : checkBlocks segment07 [segment06, segment06] 105 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block16 : checkBlocks segment07 [segment06, segment06] 112 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block17 : checkBlocks segment07 [segment06, segment06] 119 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block18 : checkBlocks segment07 [segment06, segment06] 126 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block19 : checkBlocks segment07 [segment06, segment06] 133 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block20 : checkBlocks segment07 [segment06, segment06] 140 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block21 : checkBlocks segment07 [segment06, segment06] 147 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block22 : checkBlocks segment07 [segment06, segment06] 154 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block23 : checkBlocks segment07 [segment06, segment06] 161 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block24 : checkBlocks segment07 [segment06, segment06] 168 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block25 : checkBlocks segment07 [segment06, segment06] 175 7 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem block26 : checkBlocks segment07 [segment06, segment06] 182 7 = true := by
  decide +kernel

theorem segment07_correct : Represents segment07 word07 := by
  refine represents_of_checks segment07 [(segment06, word06), (segment06, word06)] ?_ 7 27 (by decide) ?_
  · intro t w h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact segment06_correct
    · exact segment06_correct
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
