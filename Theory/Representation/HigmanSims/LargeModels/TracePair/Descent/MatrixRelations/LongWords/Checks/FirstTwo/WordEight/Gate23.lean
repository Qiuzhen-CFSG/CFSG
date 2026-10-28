module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.FirstTwo.Checker

/-!
# Fixed numerical product gate 23 for the HS long-word circuit

Kernel checks cover all 896 rows in consecutive ranges of sixteen. Synchronous
numerical declarations bound the reduction cache without changing thread counts
or arithmetic budgets. See `FirstTwo/source/README.md`; the matrices and their
ATLAS provenance remain in the shared LongWords and TracePair source modules.
-/

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo.WordEight.Gate23

private theorem assemble
    (h0 : CheckedRange 23 0 16)
    (h1 : CheckedRange 23 16 16)
    (h2 : CheckedRange 23 32 16)
    (h3 : CheckedRange 23 48 16)
    (h4 : CheckedRange 23 64 16)
    (h5 : CheckedRange 23 80 16)
    (h6 : CheckedRange 23 96 16)
    (h7 : CheckedRange 23 112 16)
    (h8 : CheckedRange 23 128 16)
    (h9 : CheckedRange 23 144 16)
    (h10 : CheckedRange 23 160 16)
    (h11 : CheckedRange 23 176 16)
    (h12 : CheckedRange 23 192 16)
    (h13 : CheckedRange 23 208 16)
    (h14 : CheckedRange 23 224 16)
    (h15 : CheckedRange 23 240 16)
    (h16 : CheckedRange 23 256 16)
    (h17 : CheckedRange 23 272 16)
    (h18 : CheckedRange 23 288 16)
    (h19 : CheckedRange 23 304 16)
    (h20 : CheckedRange 23 320 16)
    (h21 : CheckedRange 23 336 16)
    (h22 : CheckedRange 23 352 16)
    (h23 : CheckedRange 23 368 16)
    (h24 : CheckedRange 23 384 16)
    (h25 : CheckedRange 23 400 16)
    (h26 : CheckedRange 23 416 16)
    (h27 : CheckedRange 23 432 16)
    (h28 : CheckedRange 23 448 16)
    (h29 : CheckedRange 23 464 16)
    (h30 : CheckedRange 23 480 16)
    (h31 : CheckedRange 23 496 16)
    (h32 : CheckedRange 23 512 16)
    (h33 : CheckedRange 23 528 16)
    (h34 : CheckedRange 23 544 16)
    (h35 : CheckedRange 23 560 16)
    (h36 : CheckedRange 23 576 16)
    (h37 : CheckedRange 23 592 16)
    (h38 : CheckedRange 23 608 16)
    (h39 : CheckedRange 23 624 16)
    (h40 : CheckedRange 23 640 16)
    (h41 : CheckedRange 23 656 16)
    (h42 : CheckedRange 23 672 16)
    (h43 : CheckedRange 23 688 16)
    (h44 : CheckedRange 23 704 16)
    (h45 : CheckedRange 23 720 16)
    (h46 : CheckedRange 23 736 16)
    (h47 : CheckedRange 23 752 16)
    (h48 : CheckedRange 23 768 16)
    (h49 : CheckedRange 23 784 16)
    (h50 : CheckedRange 23 800 16)
    (h51 : CheckedRange 23 816 16)
    (h52 : CheckedRange 23 832 16)
    (h53 : CheckedRange 23 848 16)
    (h54 : CheckedRange 23 864 16)
    (h55 : CheckedRange 23 880 16)
    : CheckedRange 23 0 896 :=
  checkedRange_append 23 0 16 880 h0 (
  checkedRange_append 23 16 16 864 h1 (
  checkedRange_append 23 32 16 848 h2 (
  checkedRange_append 23 48 16 832 h3 (
  checkedRange_append 23 64 16 816 h4 (
  checkedRange_append 23 80 16 800 h5 (
  checkedRange_append 23 96 16 784 h6 (
  checkedRange_append 23 112 16 768 h7 (
  checkedRange_append 23 128 16 752 h8 (
  checkedRange_append 23 144 16 736 h9 (
  checkedRange_append 23 160 16 720 h10 (
  checkedRange_append 23 176 16 704 h11 (
  checkedRange_append 23 192 16 688 h12 (
  checkedRange_append 23 208 16 672 h13 (
  checkedRange_append 23 224 16 656 h14 (
  checkedRange_append 23 240 16 640 h15 (
  checkedRange_append 23 256 16 624 h16 (
  checkedRange_append 23 272 16 608 h17 (
  checkedRange_append 23 288 16 592 h18 (
  checkedRange_append 23 304 16 576 h19 (
  checkedRange_append 23 320 16 560 h20 (
  checkedRange_append 23 336 16 544 h21 (
  checkedRange_append 23 352 16 528 h22 (
  checkedRange_append 23 368 16 512 h23 (
  checkedRange_append 23 384 16 496 h24 (
  checkedRange_append 23 400 16 480 h25 (
  checkedRange_append 23 416 16 464 h26 (
  checkedRange_append 23 432 16 448 h27 (
  checkedRange_append 23 448 16 432 h28 (
  checkedRange_append 23 464 16 416 h29 (
  checkedRange_append 23 480 16 400 h30 (
  checkedRange_append 23 496 16 384 h31 (
  checkedRange_append 23 512 16 368 h32 (
  checkedRange_append 23 528 16 352 h33 (
  checkedRange_append 23 544 16 336 h34 (
  checkedRange_append 23 560 16 320 h35 (
  checkedRange_append 23 576 16 304 h36 (
  checkedRange_append 23 592 16 288 h37 (
  checkedRange_append 23 608 16 272 h38 (
  checkedRange_append 23 624 16 256 h39 (
  checkedRange_append 23 640 16 240 h40 (
  checkedRange_append 23 656 16 224 h41 (
  checkedRange_append 23 672 16 208 h42 (
  checkedRange_append 23 688 16 192 h43 (
  checkedRange_append 23 704 16 176 h44 (
  checkedRange_append 23 720 16 160 h45 (
  checkedRange_append 23 736 16 144 h46 (
  checkedRange_append 23 752 16 128 h47 (
  checkedRange_append 23 768 16 112 h48 (
  checkedRange_append 23 784 16 96 h49 (
  checkedRange_append 23 800 16 80 h50 (
  checkedRange_append 23 816 16 64 h51 (
  checkedRange_append 23 832 16 48 h52 (
  checkedRange_append 23 848 16 32 h53 (
  checkedRange_append 23 864 16 16 h54 (
  h55)))))))))))))))))))))))))))))))))))))))))))))))))))))))

set_option Elab.async false in
private theorem block0 : CheckedRange 23 0 16 :=
  checkedRange_of_check 23 0 16 (by decide +kernel)

set_option Elab.async false in
private theorem block1 : CheckedRange 23 16 16 :=
  checkedRange_of_check 23 16 16 (by decide +kernel)

set_option Elab.async false in
private theorem block2 : CheckedRange 23 32 16 :=
  checkedRange_of_check 23 32 16 (by decide +kernel)

set_option Elab.async false in
private theorem block3 : CheckedRange 23 48 16 :=
  checkedRange_of_check 23 48 16 (by decide +kernel)

set_option Elab.async false in
private theorem block4 : CheckedRange 23 64 16 :=
  checkedRange_of_check 23 64 16 (by decide +kernel)

set_option Elab.async false in
private theorem block5 : CheckedRange 23 80 16 :=
  checkedRange_of_check 23 80 16 (by decide +kernel)

set_option Elab.async false in
private theorem block6 : CheckedRange 23 96 16 :=
  checkedRange_of_check 23 96 16 (by decide +kernel)

set_option Elab.async false in
private theorem block7 : CheckedRange 23 112 16 :=
  checkedRange_of_check 23 112 16 (by decide +kernel)

set_option Elab.async false in
private theorem block8 : CheckedRange 23 128 16 :=
  checkedRange_of_check 23 128 16 (by decide +kernel)

set_option Elab.async false in
private theorem block9 : CheckedRange 23 144 16 :=
  checkedRange_of_check 23 144 16 (by decide +kernel)

set_option Elab.async false in
private theorem block10 : CheckedRange 23 160 16 :=
  checkedRange_of_check 23 160 16 (by decide +kernel)

set_option Elab.async false in
private theorem block11 : CheckedRange 23 176 16 :=
  checkedRange_of_check 23 176 16 (by decide +kernel)

set_option Elab.async false in
private theorem block12 : CheckedRange 23 192 16 :=
  checkedRange_of_check 23 192 16 (by decide +kernel)

set_option Elab.async false in
private theorem block13 : CheckedRange 23 208 16 :=
  checkedRange_of_check 23 208 16 (by decide +kernel)

set_option Elab.async false in
private theorem block14 : CheckedRange 23 224 16 :=
  checkedRange_of_check 23 224 16 (by decide +kernel)

set_option Elab.async false in
private theorem block15 : CheckedRange 23 240 16 :=
  checkedRange_of_check 23 240 16 (by decide +kernel)

set_option Elab.async false in
private theorem block16 : CheckedRange 23 256 16 :=
  checkedRange_of_check 23 256 16 (by decide +kernel)

set_option Elab.async false in
private theorem block17 : CheckedRange 23 272 16 :=
  checkedRange_of_check 23 272 16 (by decide +kernel)

set_option Elab.async false in
private theorem block18 : CheckedRange 23 288 16 :=
  checkedRange_of_check 23 288 16 (by decide +kernel)

set_option Elab.async false in
private theorem block19 : CheckedRange 23 304 16 :=
  checkedRange_of_check 23 304 16 (by decide +kernel)

set_option Elab.async false in
private theorem block20 : CheckedRange 23 320 16 :=
  checkedRange_of_check 23 320 16 (by decide +kernel)

set_option Elab.async false in
private theorem block21 : CheckedRange 23 336 16 :=
  checkedRange_of_check 23 336 16 (by decide +kernel)

set_option Elab.async false in
private theorem block22 : CheckedRange 23 352 16 :=
  checkedRange_of_check 23 352 16 (by decide +kernel)

set_option Elab.async false in
private theorem block23 : CheckedRange 23 368 16 :=
  checkedRange_of_check 23 368 16 (by decide +kernel)

set_option Elab.async false in
private theorem block24 : CheckedRange 23 384 16 :=
  checkedRange_of_check 23 384 16 (by decide +kernel)

set_option Elab.async false in
private theorem block25 : CheckedRange 23 400 16 :=
  checkedRange_of_check 23 400 16 (by decide +kernel)

set_option Elab.async false in
private theorem block26 : CheckedRange 23 416 16 :=
  checkedRange_of_check 23 416 16 (by decide +kernel)

set_option Elab.async false in
private theorem block27 : CheckedRange 23 432 16 :=
  checkedRange_of_check 23 432 16 (by decide +kernel)

set_option Elab.async false in
private theorem block28 : CheckedRange 23 448 16 :=
  checkedRange_of_check 23 448 16 (by decide +kernel)

set_option Elab.async false in
private theorem block29 : CheckedRange 23 464 16 :=
  checkedRange_of_check 23 464 16 (by decide +kernel)

set_option Elab.async false in
private theorem block30 : CheckedRange 23 480 16 :=
  checkedRange_of_check 23 480 16 (by decide +kernel)

set_option Elab.async false in
private theorem block31 : CheckedRange 23 496 16 :=
  checkedRange_of_check 23 496 16 (by decide +kernel)

set_option Elab.async false in
private theorem block32 : CheckedRange 23 512 16 :=
  checkedRange_of_check 23 512 16 (by decide +kernel)

set_option Elab.async false in
private theorem block33 : CheckedRange 23 528 16 :=
  checkedRange_of_check 23 528 16 (by decide +kernel)

set_option Elab.async false in
private theorem block34 : CheckedRange 23 544 16 :=
  checkedRange_of_check 23 544 16 (by decide +kernel)

set_option Elab.async false in
private theorem block35 : CheckedRange 23 560 16 :=
  checkedRange_of_check 23 560 16 (by decide +kernel)

set_option Elab.async false in
private theorem block36 : CheckedRange 23 576 16 :=
  checkedRange_of_check 23 576 16 (by decide +kernel)

set_option Elab.async false in
private theorem block37 : CheckedRange 23 592 16 :=
  checkedRange_of_check 23 592 16 (by decide +kernel)

set_option Elab.async false in
private theorem block38 : CheckedRange 23 608 16 :=
  checkedRange_of_check 23 608 16 (by decide +kernel)

set_option Elab.async false in
private theorem block39 : CheckedRange 23 624 16 :=
  checkedRange_of_check 23 624 16 (by decide +kernel)

set_option Elab.async false in
private theorem block40 : CheckedRange 23 640 16 :=
  checkedRange_of_check 23 640 16 (by decide +kernel)

set_option Elab.async false in
private theorem block41 : CheckedRange 23 656 16 :=
  checkedRange_of_check 23 656 16 (by decide +kernel)

set_option Elab.async false in
private theorem block42 : CheckedRange 23 672 16 :=
  checkedRange_of_check 23 672 16 (by decide +kernel)

set_option Elab.async false in
private theorem block43 : CheckedRange 23 688 16 :=
  checkedRange_of_check 23 688 16 (by decide +kernel)

set_option Elab.async false in
private theorem block44 : CheckedRange 23 704 16 :=
  checkedRange_of_check 23 704 16 (by decide +kernel)

set_option Elab.async false in
private theorem block45 : CheckedRange 23 720 16 :=
  checkedRange_of_check 23 720 16 (by decide +kernel)

set_option Elab.async false in
private theorem block46 : CheckedRange 23 736 16 :=
  checkedRange_of_check 23 736 16 (by decide +kernel)

set_option Elab.async false in
private theorem block47 : CheckedRange 23 752 16 :=
  checkedRange_of_check 23 752 16 (by decide +kernel)

set_option Elab.async false in
private theorem block48 : CheckedRange 23 768 16 :=
  checkedRange_of_check 23 768 16 (by decide +kernel)

set_option Elab.async false in
private theorem block49 : CheckedRange 23 784 16 :=
  checkedRange_of_check 23 784 16 (by decide +kernel)

set_option Elab.async false in
private theorem block50 : CheckedRange 23 800 16 :=
  checkedRange_of_check 23 800 16 (by decide +kernel)

set_option Elab.async false in
private theorem block51 : CheckedRange 23 816 16 :=
  checkedRange_of_check 23 816 16 (by decide +kernel)

set_option Elab.async false in
private theorem block52 : CheckedRange 23 832 16 :=
  checkedRange_of_check 23 832 16 (by decide +kernel)

set_option Elab.async false in
private theorem block53 : CheckedRange 23 848 16 :=
  checkedRange_of_check 23 848 16 (by decide +kernel)

set_option Elab.async false in
private theorem block54 : CheckedRange 23 864 16 :=
  checkedRange_of_check 23 864 16 (by decide +kernel)

set_option Elab.async false in
private theorem block55 : CheckedRange 23 880 16 :=
  checkedRange_of_check 23 880 16 (by decide +kernel)

/-- All rows of the literal gate, with no earlier gate assumptions. -/
theorem product_check : ProductCheck 23 :=
  productCheck_of_checkedRange 23 (assemble
    block0 block1 block2 block3 block4 block5 block6 block7 block8 block9 block10 block11 block12 block13 block14 block15 block16 block17 block18 block19 block20 block21 block22 block23 block24 block25 block26 block27 block28 block29 block30 block31 block32 block33 block34 block35 block36 block37 block38 block39 block40 block41 block42 block43 block44 block45 block46 block47 block48 block49 block50 block51 block52 block53 block54 block55)

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.FirstTwo.WordEight.Gate23
