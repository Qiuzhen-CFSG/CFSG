module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Checker
import Mathlib.Tactic.FinCases

/-!
# Literal product gate 26

Kernel-checked multiplication of candidates 16 and 17, with output 28.
Sixteen-row certificates cover all 896 rows. The checked evaluator is the
original GF(4) accumulator; no earlier gate's word interpretation is used.
See `Lower/source/README.md` for sources and the full-gate benchmark.
-/

-- Bound concurrent kernel reductions, leaving Lean's process threading unchanged.
set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
open Certificates Packed

private theorem gate26_block00 :
    check rows17 ((rows16.drop 0).take 16)
      ((rows28.drop 0).take 16) = true := by decide +kernel

private theorem gate26_block01 :
    check rows17 ((rows16.drop 16).take 16)
      ((rows28.drop 16).take 16) = true := by decide +kernel

private theorem gate26_block02 :
    check rows17 ((rows16.drop 32).take 16)
      ((rows28.drop 32).take 16) = true := by decide +kernel

private theorem gate26_block03 :
    check rows17 ((rows16.drop 48).take 16)
      ((rows28.drop 48).take 16) = true := by decide +kernel

private theorem gate26_block04 :
    check rows17 ((rows16.drop 64).take 16)
      ((rows28.drop 64).take 16) = true := by decide +kernel

private theorem gate26_block05 :
    check rows17 ((rows16.drop 80).take 16)
      ((rows28.drop 80).take 16) = true := by decide +kernel

private theorem gate26_block06 :
    check rows17 ((rows16.drop 96).take 16)
      ((rows28.drop 96).take 16) = true := by decide +kernel

private theorem gate26_block07 :
    check rows17 ((rows16.drop 112).take 16)
      ((rows28.drop 112).take 16) = true := by decide +kernel

private theorem gate26_block08 :
    check rows17 ((rows16.drop 128).take 16)
      ((rows28.drop 128).take 16) = true := by decide +kernel

private theorem gate26_block09 :
    check rows17 ((rows16.drop 144).take 16)
      ((rows28.drop 144).take 16) = true := by decide +kernel

private theorem gate26_block10 :
    check rows17 ((rows16.drop 160).take 16)
      ((rows28.drop 160).take 16) = true := by decide +kernel

private theorem gate26_block11 :
    check rows17 ((rows16.drop 176).take 16)
      ((rows28.drop 176).take 16) = true := by decide +kernel

private theorem gate26_block12 :
    check rows17 ((rows16.drop 192).take 16)
      ((rows28.drop 192).take 16) = true := by decide +kernel

private theorem gate26_block13 :
    check rows17 ((rows16.drop 208).take 16)
      ((rows28.drop 208).take 16) = true := by decide +kernel

private theorem gate26_block14 :
    check rows17 ((rows16.drop 224).take 16)
      ((rows28.drop 224).take 16) = true := by decide +kernel

private theorem gate26_block15 :
    check rows17 ((rows16.drop 240).take 16)
      ((rows28.drop 240).take 16) = true := by decide +kernel

private theorem gate26_block16 :
    check rows17 ((rows16.drop 256).take 16)
      ((rows28.drop 256).take 16) = true := by decide +kernel

private theorem gate26_block17 :
    check rows17 ((rows16.drop 272).take 16)
      ((rows28.drop 272).take 16) = true := by decide +kernel

private theorem gate26_block18 :
    check rows17 ((rows16.drop 288).take 16)
      ((rows28.drop 288).take 16) = true := by decide +kernel

private theorem gate26_block19 :
    check rows17 ((rows16.drop 304).take 16)
      ((rows28.drop 304).take 16) = true := by decide +kernel

private theorem gate26_block20 :
    check rows17 ((rows16.drop 320).take 16)
      ((rows28.drop 320).take 16) = true := by decide +kernel

private theorem gate26_block21 :
    check rows17 ((rows16.drop 336).take 16)
      ((rows28.drop 336).take 16) = true := by decide +kernel

private theorem gate26_block22 :
    check rows17 ((rows16.drop 352).take 16)
      ((rows28.drop 352).take 16) = true := by decide +kernel

private theorem gate26_block23 :
    check rows17 ((rows16.drop 368).take 16)
      ((rows28.drop 368).take 16) = true := by decide +kernel

private theorem gate26_block24 :
    check rows17 ((rows16.drop 384).take 16)
      ((rows28.drop 384).take 16) = true := by decide +kernel

private theorem gate26_block25 :
    check rows17 ((rows16.drop 400).take 16)
      ((rows28.drop 400).take 16) = true := by decide +kernel

private theorem gate26_block26 :
    check rows17 ((rows16.drop 416).take 16)
      ((rows28.drop 416).take 16) = true := by decide +kernel

private theorem gate26_block27 :
    check rows17 ((rows16.drop 432).take 16)
      ((rows28.drop 432).take 16) = true := by decide +kernel

private theorem gate26_block28 :
    check rows17 ((rows16.drop 448).take 16)
      ((rows28.drop 448).take 16) = true := by decide +kernel

private theorem gate26_block29 :
    check rows17 ((rows16.drop 464).take 16)
      ((rows28.drop 464).take 16) = true := by decide +kernel

private theorem gate26_block30 :
    check rows17 ((rows16.drop 480).take 16)
      ((rows28.drop 480).take 16) = true := by decide +kernel

private theorem gate26_block31 :
    check rows17 ((rows16.drop 496).take 16)
      ((rows28.drop 496).take 16) = true := by decide +kernel

private theorem gate26_block32 :
    check rows17 ((rows16.drop 512).take 16)
      ((rows28.drop 512).take 16) = true := by decide +kernel

private theorem gate26_block33 :
    check rows17 ((rows16.drop 528).take 16)
      ((rows28.drop 528).take 16) = true := by decide +kernel

private theorem gate26_block34 :
    check rows17 ((rows16.drop 544).take 16)
      ((rows28.drop 544).take 16) = true := by decide +kernel

private theorem gate26_block35 :
    check rows17 ((rows16.drop 560).take 16)
      ((rows28.drop 560).take 16) = true := by decide +kernel

private theorem gate26_block36 :
    check rows17 ((rows16.drop 576).take 16)
      ((rows28.drop 576).take 16) = true := by decide +kernel

private theorem gate26_block37 :
    check rows17 ((rows16.drop 592).take 16)
      ((rows28.drop 592).take 16) = true := by decide +kernel

private theorem gate26_block38 :
    check rows17 ((rows16.drop 608).take 16)
      ((rows28.drop 608).take 16) = true := by decide +kernel

private theorem gate26_block39 :
    check rows17 ((rows16.drop 624).take 16)
      ((rows28.drop 624).take 16) = true := by decide +kernel

private theorem gate26_block40 :
    check rows17 ((rows16.drop 640).take 16)
      ((rows28.drop 640).take 16) = true := by decide +kernel

private theorem gate26_block41 :
    check rows17 ((rows16.drop 656).take 16)
      ((rows28.drop 656).take 16) = true := by decide +kernel

private theorem gate26_block42 :
    check rows17 ((rows16.drop 672).take 16)
      ((rows28.drop 672).take 16) = true := by decide +kernel

private theorem gate26_block43 :
    check rows17 ((rows16.drop 688).take 16)
      ((rows28.drop 688).take 16) = true := by decide +kernel

private theorem gate26_block44 :
    check rows17 ((rows16.drop 704).take 16)
      ((rows28.drop 704).take 16) = true := by decide +kernel

private theorem gate26_block45 :
    check rows17 ((rows16.drop 720).take 16)
      ((rows28.drop 720).take 16) = true := by decide +kernel

private theorem gate26_block46 :
    check rows17 ((rows16.drop 736).take 16)
      ((rows28.drop 736).take 16) = true := by decide +kernel

private theorem gate26_block47 :
    check rows17 ((rows16.drop 752).take 16)
      ((rows28.drop 752).take 16) = true := by decide +kernel

private theorem gate26_block48 :
    check rows17 ((rows16.drop 768).take 16)
      ((rows28.drop 768).take 16) = true := by decide +kernel

private theorem gate26_block49 :
    check rows17 ((rows16.drop 784).take 16)
      ((rows28.drop 784).take 16) = true := by decide +kernel

private theorem gate26_block50 :
    check rows17 ((rows16.drop 800).take 16)
      ((rows28.drop 800).take 16) = true := by decide +kernel

private theorem gate26_block51 :
    check rows17 ((rows16.drop 816).take 16)
      ((rows28.drop 816).take 16) = true := by decide +kernel

private theorem gate26_block52 :
    check rows17 ((rows16.drop 832).take 16)
      ((rows28.drop 832).take 16) = true := by decide +kernel

private theorem gate26_block53 :
    check rows17 ((rows16.drop 848).take 16)
      ((rows28.drop 848).take 16) = true := by decide +kernel

private theorem gate26_block54 :
    check rows17 ((rows16.drop 864).take 16)
      ((rows28.drop 864).take 16) = true := by decide +kernel

private theorem gate26_block55 :
    check rows17 ((rows16.drop 880).take 16)
      ((rows28.drop 880).take 16) = true := by decide +kernel

private theorem gate26_blocks (b : Fin 56) :
    check rows17 ((rows16.drop (16*b.val)).take 16)
      ((rows28.drop (16*b.val)).take 16) = true := by
  fin_cases b
  · exact gate26_block00
  · exact gate26_block01
  · exact gate26_block02
  · exact gate26_block03
  · exact gate26_block04
  · exact gate26_block05
  · exact gate26_block06
  · exact gate26_block07
  · exact gate26_block08
  · exact gate26_block09
  · exact gate26_block10
  · exact gate26_block11
  · exact gate26_block12
  · exact gate26_block13
  · exact gate26_block14
  · exact gate26_block15
  · exact gate26_block16
  · exact gate26_block17
  · exact gate26_block18
  · exact gate26_block19
  · exact gate26_block20
  · exact gate26_block21
  · exact gate26_block22
  · exact gate26_block23
  · exact gate26_block24
  · exact gate26_block25
  · exact gate26_block26
  · exact gate26_block27
  · exact gate26_block28
  · exact gate26_block29
  · exact gate26_block30
  · exact gate26_block31
  · exact gate26_block32
  · exact gate26_block33
  · exact gate26_block34
  · exact gate26_block35
  · exact gate26_block36
  · exact gate26_block37
  · exact gate26_block38
  · exact gate26_block39
  · exact gate26_block40
  · exact gate26_block41
  · exact gate26_block42
  · exact gate26_block43
  · exact gate26_block44
  · exact gate26_block45
  · exact gate26_block46
  · exact gate26_block47
  · exact gate26_block48
  · exact gate26_block49
  · exact gate26_block50
  · exact gate26_block51
  · exact gate26_block52
  · exact gate26_block53
  · exact gate26_block54
  · exact gate26_block55

/-- The complete fixed product, certified on every row. -/
theorem product_26 : ProductCheck 26 := by
  apply productCheck_of_rows
  intro r
  exact block_sound rows16 rows17 rows28 16 (16*(r.val/16))
    (gate26_blocks ⟨r.val/16, by omega⟩) rows16_length r.val (by omega) (by omega) r.isLt

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
