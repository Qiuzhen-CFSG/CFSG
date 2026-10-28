module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Checker
import Mathlib.Tactic.FinCases

/-!
# Literal product gate 29

Kernel-checked multiplication of candidates 8 and 7, with output 31.
Sixteen-row certificates cover all 896 rows. The checked evaluator is the
original GF(4) accumulator; no earlier gate's word interpretation is used.
See `Lower/source/README.md` for sources and the full-gate benchmark.
-/

-- Bound concurrent kernel reductions, leaving Lean's process threading unchanged.
set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
open Certificates Packed

private theorem gate29_block00 :
    check rows07 ((rows08.drop 0).take 16)
      ((rows31.drop 0).take 16) = true := by decide +kernel

private theorem gate29_block01 :
    check rows07 ((rows08.drop 16).take 16)
      ((rows31.drop 16).take 16) = true := by decide +kernel

private theorem gate29_block02 :
    check rows07 ((rows08.drop 32).take 16)
      ((rows31.drop 32).take 16) = true := by decide +kernel

private theorem gate29_block03 :
    check rows07 ((rows08.drop 48).take 16)
      ((rows31.drop 48).take 16) = true := by decide +kernel

private theorem gate29_block04 :
    check rows07 ((rows08.drop 64).take 16)
      ((rows31.drop 64).take 16) = true := by decide +kernel

private theorem gate29_block05 :
    check rows07 ((rows08.drop 80).take 16)
      ((rows31.drop 80).take 16) = true := by decide +kernel

private theorem gate29_block06 :
    check rows07 ((rows08.drop 96).take 16)
      ((rows31.drop 96).take 16) = true := by decide +kernel

private theorem gate29_block07 :
    check rows07 ((rows08.drop 112).take 16)
      ((rows31.drop 112).take 16) = true := by decide +kernel

private theorem gate29_block08 :
    check rows07 ((rows08.drop 128).take 16)
      ((rows31.drop 128).take 16) = true := by decide +kernel

private theorem gate29_block09 :
    check rows07 ((rows08.drop 144).take 16)
      ((rows31.drop 144).take 16) = true := by decide +kernel

private theorem gate29_block10 :
    check rows07 ((rows08.drop 160).take 16)
      ((rows31.drop 160).take 16) = true := by decide +kernel

private theorem gate29_block11 :
    check rows07 ((rows08.drop 176).take 16)
      ((rows31.drop 176).take 16) = true := by decide +kernel

private theorem gate29_block12 :
    check rows07 ((rows08.drop 192).take 16)
      ((rows31.drop 192).take 16) = true := by decide +kernel

private theorem gate29_block13 :
    check rows07 ((rows08.drop 208).take 16)
      ((rows31.drop 208).take 16) = true := by decide +kernel

private theorem gate29_block14 :
    check rows07 ((rows08.drop 224).take 16)
      ((rows31.drop 224).take 16) = true := by decide +kernel

private theorem gate29_block15 :
    check rows07 ((rows08.drop 240).take 16)
      ((rows31.drop 240).take 16) = true := by decide +kernel

private theorem gate29_block16 :
    check rows07 ((rows08.drop 256).take 16)
      ((rows31.drop 256).take 16) = true := by decide +kernel

private theorem gate29_block17 :
    check rows07 ((rows08.drop 272).take 16)
      ((rows31.drop 272).take 16) = true := by decide +kernel

private theorem gate29_block18 :
    check rows07 ((rows08.drop 288).take 16)
      ((rows31.drop 288).take 16) = true := by decide +kernel

private theorem gate29_block19 :
    check rows07 ((rows08.drop 304).take 16)
      ((rows31.drop 304).take 16) = true := by decide +kernel

private theorem gate29_block20 :
    check rows07 ((rows08.drop 320).take 16)
      ((rows31.drop 320).take 16) = true := by decide +kernel

private theorem gate29_block21 :
    check rows07 ((rows08.drop 336).take 16)
      ((rows31.drop 336).take 16) = true := by decide +kernel

private theorem gate29_block22 :
    check rows07 ((rows08.drop 352).take 16)
      ((rows31.drop 352).take 16) = true := by decide +kernel

private theorem gate29_block23 :
    check rows07 ((rows08.drop 368).take 16)
      ((rows31.drop 368).take 16) = true := by decide +kernel

private theorem gate29_block24 :
    check rows07 ((rows08.drop 384).take 16)
      ((rows31.drop 384).take 16) = true := by decide +kernel

private theorem gate29_block25 :
    check rows07 ((rows08.drop 400).take 16)
      ((rows31.drop 400).take 16) = true := by decide +kernel

private theorem gate29_block26 :
    check rows07 ((rows08.drop 416).take 16)
      ((rows31.drop 416).take 16) = true := by decide +kernel

private theorem gate29_block27 :
    check rows07 ((rows08.drop 432).take 16)
      ((rows31.drop 432).take 16) = true := by decide +kernel

private theorem gate29_block28 :
    check rows07 ((rows08.drop 448).take 16)
      ((rows31.drop 448).take 16) = true := by decide +kernel

private theorem gate29_block29 :
    check rows07 ((rows08.drop 464).take 16)
      ((rows31.drop 464).take 16) = true := by decide +kernel

private theorem gate29_block30 :
    check rows07 ((rows08.drop 480).take 16)
      ((rows31.drop 480).take 16) = true := by decide +kernel

private theorem gate29_block31 :
    check rows07 ((rows08.drop 496).take 16)
      ((rows31.drop 496).take 16) = true := by decide +kernel

private theorem gate29_block32 :
    check rows07 ((rows08.drop 512).take 16)
      ((rows31.drop 512).take 16) = true := by decide +kernel

private theorem gate29_block33 :
    check rows07 ((rows08.drop 528).take 16)
      ((rows31.drop 528).take 16) = true := by decide +kernel

private theorem gate29_block34 :
    check rows07 ((rows08.drop 544).take 16)
      ((rows31.drop 544).take 16) = true := by decide +kernel

private theorem gate29_block35 :
    check rows07 ((rows08.drop 560).take 16)
      ((rows31.drop 560).take 16) = true := by decide +kernel

private theorem gate29_block36 :
    check rows07 ((rows08.drop 576).take 16)
      ((rows31.drop 576).take 16) = true := by decide +kernel

private theorem gate29_block37 :
    check rows07 ((rows08.drop 592).take 16)
      ((rows31.drop 592).take 16) = true := by decide +kernel

private theorem gate29_block38 :
    check rows07 ((rows08.drop 608).take 16)
      ((rows31.drop 608).take 16) = true := by decide +kernel

private theorem gate29_block39 :
    check rows07 ((rows08.drop 624).take 16)
      ((rows31.drop 624).take 16) = true := by decide +kernel

private theorem gate29_block40 :
    check rows07 ((rows08.drop 640).take 16)
      ((rows31.drop 640).take 16) = true := by decide +kernel

private theorem gate29_block41 :
    check rows07 ((rows08.drop 656).take 16)
      ((rows31.drop 656).take 16) = true := by decide +kernel

private theorem gate29_block42 :
    check rows07 ((rows08.drop 672).take 16)
      ((rows31.drop 672).take 16) = true := by decide +kernel

private theorem gate29_block43 :
    check rows07 ((rows08.drop 688).take 16)
      ((rows31.drop 688).take 16) = true := by decide +kernel

private theorem gate29_block44 :
    check rows07 ((rows08.drop 704).take 16)
      ((rows31.drop 704).take 16) = true := by decide +kernel

private theorem gate29_block45 :
    check rows07 ((rows08.drop 720).take 16)
      ((rows31.drop 720).take 16) = true := by decide +kernel

private theorem gate29_block46 :
    check rows07 ((rows08.drop 736).take 16)
      ((rows31.drop 736).take 16) = true := by decide +kernel

private theorem gate29_block47 :
    check rows07 ((rows08.drop 752).take 16)
      ((rows31.drop 752).take 16) = true := by decide +kernel

private theorem gate29_block48 :
    check rows07 ((rows08.drop 768).take 16)
      ((rows31.drop 768).take 16) = true := by decide +kernel

private theorem gate29_block49 :
    check rows07 ((rows08.drop 784).take 16)
      ((rows31.drop 784).take 16) = true := by decide +kernel

private theorem gate29_block50 :
    check rows07 ((rows08.drop 800).take 16)
      ((rows31.drop 800).take 16) = true := by decide +kernel

private theorem gate29_block51 :
    check rows07 ((rows08.drop 816).take 16)
      ((rows31.drop 816).take 16) = true := by decide +kernel

private theorem gate29_block52 :
    check rows07 ((rows08.drop 832).take 16)
      ((rows31.drop 832).take 16) = true := by decide +kernel

private theorem gate29_block53 :
    check rows07 ((rows08.drop 848).take 16)
      ((rows31.drop 848).take 16) = true := by decide +kernel

private theorem gate29_block54 :
    check rows07 ((rows08.drop 864).take 16)
      ((rows31.drop 864).take 16) = true := by decide +kernel

private theorem gate29_block55 :
    check rows07 ((rows08.drop 880).take 16)
      ((rows31.drop 880).take 16) = true := by decide +kernel

private theorem gate29_blocks (b : Fin 56) :
    check rows07 ((rows08.drop (16*b.val)).take 16)
      ((rows31.drop (16*b.val)).take 16) = true := by
  fin_cases b
  · exact gate29_block00
  · exact gate29_block01
  · exact gate29_block02
  · exact gate29_block03
  · exact gate29_block04
  · exact gate29_block05
  · exact gate29_block06
  · exact gate29_block07
  · exact gate29_block08
  · exact gate29_block09
  · exact gate29_block10
  · exact gate29_block11
  · exact gate29_block12
  · exact gate29_block13
  · exact gate29_block14
  · exact gate29_block15
  · exact gate29_block16
  · exact gate29_block17
  · exact gate29_block18
  · exact gate29_block19
  · exact gate29_block20
  · exact gate29_block21
  · exact gate29_block22
  · exact gate29_block23
  · exact gate29_block24
  · exact gate29_block25
  · exact gate29_block26
  · exact gate29_block27
  · exact gate29_block28
  · exact gate29_block29
  · exact gate29_block30
  · exact gate29_block31
  · exact gate29_block32
  · exact gate29_block33
  · exact gate29_block34
  · exact gate29_block35
  · exact gate29_block36
  · exact gate29_block37
  · exact gate29_block38
  · exact gate29_block39
  · exact gate29_block40
  · exact gate29_block41
  · exact gate29_block42
  · exact gate29_block43
  · exact gate29_block44
  · exact gate29_block45
  · exact gate29_block46
  · exact gate29_block47
  · exact gate29_block48
  · exact gate29_block49
  · exact gate29_block50
  · exact gate29_block51
  · exact gate29_block52
  · exact gate29_block53
  · exact gate29_block54
  · exact gate29_block55

/-- The complete fixed product, certified on every row. -/
theorem product_29 : ProductCheck 29 := by
  apply productCheck_of_rows
  intro r
  exact block_sound rows08 rows07 rows31 16 (16*(r.val/16))
    (gate29_blocks ⟨r.val/16, by omega⟩) rows08_length r.val (by omega) (by omega) r.isLt

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
