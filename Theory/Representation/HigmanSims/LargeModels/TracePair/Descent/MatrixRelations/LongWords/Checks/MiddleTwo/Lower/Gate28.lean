module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Checker
import Mathlib.Tactic.FinCases

/-!
# Literal product gate 28

Kernel-checked multiplication of candidates 3 and 14, with output 30.
Sixteen-row certificates cover all 896 rows. The checked evaluator is the
original GF(4) accumulator; no earlier gate's word interpretation is used.
See `Lower/source/README.md` for sources and the full-gate benchmark.
-/

-- Bound concurrent kernel reductions, leaving Lean's process threading unchanged.
set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
open Certificates Packed

private theorem gate28_block00 :
    check rows14 ((rows03.drop 0).take 16)
      ((rows30.drop 0).take 16) = true := by decide +kernel

private theorem gate28_block01 :
    check rows14 ((rows03.drop 16).take 16)
      ((rows30.drop 16).take 16) = true := by decide +kernel

private theorem gate28_block02 :
    check rows14 ((rows03.drop 32).take 16)
      ((rows30.drop 32).take 16) = true := by decide +kernel

private theorem gate28_block03 :
    check rows14 ((rows03.drop 48).take 16)
      ((rows30.drop 48).take 16) = true := by decide +kernel

private theorem gate28_block04 :
    check rows14 ((rows03.drop 64).take 16)
      ((rows30.drop 64).take 16) = true := by decide +kernel

private theorem gate28_block05 :
    check rows14 ((rows03.drop 80).take 16)
      ((rows30.drop 80).take 16) = true := by decide +kernel

private theorem gate28_block06 :
    check rows14 ((rows03.drop 96).take 16)
      ((rows30.drop 96).take 16) = true := by decide +kernel

private theorem gate28_block07 :
    check rows14 ((rows03.drop 112).take 16)
      ((rows30.drop 112).take 16) = true := by decide +kernel

private theorem gate28_block08 :
    check rows14 ((rows03.drop 128).take 16)
      ((rows30.drop 128).take 16) = true := by decide +kernel

private theorem gate28_block09 :
    check rows14 ((rows03.drop 144).take 16)
      ((rows30.drop 144).take 16) = true := by decide +kernel

private theorem gate28_block10 :
    check rows14 ((rows03.drop 160).take 16)
      ((rows30.drop 160).take 16) = true := by decide +kernel

private theorem gate28_block11 :
    check rows14 ((rows03.drop 176).take 16)
      ((rows30.drop 176).take 16) = true := by decide +kernel

private theorem gate28_block12 :
    check rows14 ((rows03.drop 192).take 16)
      ((rows30.drop 192).take 16) = true := by decide +kernel

private theorem gate28_block13 :
    check rows14 ((rows03.drop 208).take 16)
      ((rows30.drop 208).take 16) = true := by decide +kernel

private theorem gate28_block14 :
    check rows14 ((rows03.drop 224).take 16)
      ((rows30.drop 224).take 16) = true := by decide +kernel

private theorem gate28_block15 :
    check rows14 ((rows03.drop 240).take 16)
      ((rows30.drop 240).take 16) = true := by decide +kernel

private theorem gate28_block16 :
    check rows14 ((rows03.drop 256).take 16)
      ((rows30.drop 256).take 16) = true := by decide +kernel

private theorem gate28_block17 :
    check rows14 ((rows03.drop 272).take 16)
      ((rows30.drop 272).take 16) = true := by decide +kernel

private theorem gate28_block18 :
    check rows14 ((rows03.drop 288).take 16)
      ((rows30.drop 288).take 16) = true := by decide +kernel

private theorem gate28_block19 :
    check rows14 ((rows03.drop 304).take 16)
      ((rows30.drop 304).take 16) = true := by decide +kernel

private theorem gate28_block20 :
    check rows14 ((rows03.drop 320).take 16)
      ((rows30.drop 320).take 16) = true := by decide +kernel

private theorem gate28_block21 :
    check rows14 ((rows03.drop 336).take 16)
      ((rows30.drop 336).take 16) = true := by decide +kernel

private theorem gate28_block22 :
    check rows14 ((rows03.drop 352).take 16)
      ((rows30.drop 352).take 16) = true := by decide +kernel

private theorem gate28_block23 :
    check rows14 ((rows03.drop 368).take 16)
      ((rows30.drop 368).take 16) = true := by decide +kernel

private theorem gate28_block24 :
    check rows14 ((rows03.drop 384).take 16)
      ((rows30.drop 384).take 16) = true := by decide +kernel

private theorem gate28_block25 :
    check rows14 ((rows03.drop 400).take 16)
      ((rows30.drop 400).take 16) = true := by decide +kernel

private theorem gate28_block26 :
    check rows14 ((rows03.drop 416).take 16)
      ((rows30.drop 416).take 16) = true := by decide +kernel

private theorem gate28_block27 :
    check rows14 ((rows03.drop 432).take 16)
      ((rows30.drop 432).take 16) = true := by decide +kernel

private theorem gate28_block28 :
    check rows14 ((rows03.drop 448).take 16)
      ((rows30.drop 448).take 16) = true := by decide +kernel

private theorem gate28_block29 :
    check rows14 ((rows03.drop 464).take 16)
      ((rows30.drop 464).take 16) = true := by decide +kernel

private theorem gate28_block30 :
    check rows14 ((rows03.drop 480).take 16)
      ((rows30.drop 480).take 16) = true := by decide +kernel

private theorem gate28_block31 :
    check rows14 ((rows03.drop 496).take 16)
      ((rows30.drop 496).take 16) = true := by decide +kernel

private theorem gate28_block32 :
    check rows14 ((rows03.drop 512).take 16)
      ((rows30.drop 512).take 16) = true := by decide +kernel

private theorem gate28_block33 :
    check rows14 ((rows03.drop 528).take 16)
      ((rows30.drop 528).take 16) = true := by decide +kernel

private theorem gate28_block34 :
    check rows14 ((rows03.drop 544).take 16)
      ((rows30.drop 544).take 16) = true := by decide +kernel

private theorem gate28_block35 :
    check rows14 ((rows03.drop 560).take 16)
      ((rows30.drop 560).take 16) = true := by decide +kernel

private theorem gate28_block36 :
    check rows14 ((rows03.drop 576).take 16)
      ((rows30.drop 576).take 16) = true := by decide +kernel

private theorem gate28_block37 :
    check rows14 ((rows03.drop 592).take 16)
      ((rows30.drop 592).take 16) = true := by decide +kernel

private theorem gate28_block38 :
    check rows14 ((rows03.drop 608).take 16)
      ((rows30.drop 608).take 16) = true := by decide +kernel

private theorem gate28_block39 :
    check rows14 ((rows03.drop 624).take 16)
      ((rows30.drop 624).take 16) = true := by decide +kernel

private theorem gate28_block40 :
    check rows14 ((rows03.drop 640).take 16)
      ((rows30.drop 640).take 16) = true := by decide +kernel

private theorem gate28_block41 :
    check rows14 ((rows03.drop 656).take 16)
      ((rows30.drop 656).take 16) = true := by decide +kernel

private theorem gate28_block42 :
    check rows14 ((rows03.drop 672).take 16)
      ((rows30.drop 672).take 16) = true := by decide +kernel

private theorem gate28_block43 :
    check rows14 ((rows03.drop 688).take 16)
      ((rows30.drop 688).take 16) = true := by decide +kernel

private theorem gate28_block44 :
    check rows14 ((rows03.drop 704).take 16)
      ((rows30.drop 704).take 16) = true := by decide +kernel

private theorem gate28_block45 :
    check rows14 ((rows03.drop 720).take 16)
      ((rows30.drop 720).take 16) = true := by decide +kernel

private theorem gate28_block46 :
    check rows14 ((rows03.drop 736).take 16)
      ((rows30.drop 736).take 16) = true := by decide +kernel

private theorem gate28_block47 :
    check rows14 ((rows03.drop 752).take 16)
      ((rows30.drop 752).take 16) = true := by decide +kernel

private theorem gate28_block48 :
    check rows14 ((rows03.drop 768).take 16)
      ((rows30.drop 768).take 16) = true := by decide +kernel

private theorem gate28_block49 :
    check rows14 ((rows03.drop 784).take 16)
      ((rows30.drop 784).take 16) = true := by decide +kernel

private theorem gate28_block50 :
    check rows14 ((rows03.drop 800).take 16)
      ((rows30.drop 800).take 16) = true := by decide +kernel

private theorem gate28_block51 :
    check rows14 ((rows03.drop 816).take 16)
      ((rows30.drop 816).take 16) = true := by decide +kernel

private theorem gate28_block52 :
    check rows14 ((rows03.drop 832).take 16)
      ((rows30.drop 832).take 16) = true := by decide +kernel

private theorem gate28_block53 :
    check rows14 ((rows03.drop 848).take 16)
      ((rows30.drop 848).take 16) = true := by decide +kernel

private theorem gate28_block54 :
    check rows14 ((rows03.drop 864).take 16)
      ((rows30.drop 864).take 16) = true := by decide +kernel

private theorem gate28_block55 :
    check rows14 ((rows03.drop 880).take 16)
      ((rows30.drop 880).take 16) = true := by decide +kernel

private theorem gate28_blocks (b : Fin 56) :
    check rows14 ((rows03.drop (16*b.val)).take 16)
      ((rows30.drop (16*b.val)).take 16) = true := by
  fin_cases b
  · exact gate28_block00
  · exact gate28_block01
  · exact gate28_block02
  · exact gate28_block03
  · exact gate28_block04
  · exact gate28_block05
  · exact gate28_block06
  · exact gate28_block07
  · exact gate28_block08
  · exact gate28_block09
  · exact gate28_block10
  · exact gate28_block11
  · exact gate28_block12
  · exact gate28_block13
  · exact gate28_block14
  · exact gate28_block15
  · exact gate28_block16
  · exact gate28_block17
  · exact gate28_block18
  · exact gate28_block19
  · exact gate28_block20
  · exact gate28_block21
  · exact gate28_block22
  · exact gate28_block23
  · exact gate28_block24
  · exact gate28_block25
  · exact gate28_block26
  · exact gate28_block27
  · exact gate28_block28
  · exact gate28_block29
  · exact gate28_block30
  · exact gate28_block31
  · exact gate28_block32
  · exact gate28_block33
  · exact gate28_block34
  · exact gate28_block35
  · exact gate28_block36
  · exact gate28_block37
  · exact gate28_block38
  · exact gate28_block39
  · exact gate28_block40
  · exact gate28_block41
  · exact gate28_block42
  · exact gate28_block43
  · exact gate28_block44
  · exact gate28_block45
  · exact gate28_block46
  · exact gate28_block47
  · exact gate28_block48
  · exact gate28_block49
  · exact gate28_block50
  · exact gate28_block51
  · exact gate28_block52
  · exact gate28_block53
  · exact gate28_block54
  · exact gate28_block55

/-- The complete fixed product, certified on every row. -/
theorem product_28 : ProductCheck 28 := by
  apply productCheck_of_rows
  intro r
  exact block_sound rows03 rows14 rows30 16 (16*(r.val/16))
    (gate28_blocks ⟨r.val/16, by omega⟩) rows03_length r.val (by omega) (by omega) r.isLt

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
