module

public import Theory.Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.Checks.MiddleTwo.Lower.Checker
import Mathlib.Tactic.FinCases

/-!
# Literal product gate 27

Kernel-checked multiplication of candidates 8 and 5, with output 29.
Sixteen-row certificates cover all 896 rows. The checked evaluator is the
original GF(4) accumulator; no earlier gate's word interpretation is used.
See `Lower/source/README.md` for sources and the full-gate benchmark.
-/

-- Bound concurrent kernel reductions, leaving Lean's process threading unchanged.
set_option Elab.async false

public section
namespace Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
open Certificates Packed

private theorem gate27_block00 :
    check rows05 ((rows08.drop 0).take 16)
      ((rows29.drop 0).take 16) = true := by decide +kernel

private theorem gate27_block01 :
    check rows05 ((rows08.drop 16).take 16)
      ((rows29.drop 16).take 16) = true := by decide +kernel

private theorem gate27_block02 :
    check rows05 ((rows08.drop 32).take 16)
      ((rows29.drop 32).take 16) = true := by decide +kernel

private theorem gate27_block03 :
    check rows05 ((rows08.drop 48).take 16)
      ((rows29.drop 48).take 16) = true := by decide +kernel

private theorem gate27_block04 :
    check rows05 ((rows08.drop 64).take 16)
      ((rows29.drop 64).take 16) = true := by decide +kernel

private theorem gate27_block05 :
    check rows05 ((rows08.drop 80).take 16)
      ((rows29.drop 80).take 16) = true := by decide +kernel

private theorem gate27_block06 :
    check rows05 ((rows08.drop 96).take 16)
      ((rows29.drop 96).take 16) = true := by decide +kernel

private theorem gate27_block07 :
    check rows05 ((rows08.drop 112).take 16)
      ((rows29.drop 112).take 16) = true := by decide +kernel

private theorem gate27_block08 :
    check rows05 ((rows08.drop 128).take 16)
      ((rows29.drop 128).take 16) = true := by decide +kernel

private theorem gate27_block09 :
    check rows05 ((rows08.drop 144).take 16)
      ((rows29.drop 144).take 16) = true := by decide +kernel

private theorem gate27_block10 :
    check rows05 ((rows08.drop 160).take 16)
      ((rows29.drop 160).take 16) = true := by decide +kernel

private theorem gate27_block11 :
    check rows05 ((rows08.drop 176).take 16)
      ((rows29.drop 176).take 16) = true := by decide +kernel

private theorem gate27_block12 :
    check rows05 ((rows08.drop 192).take 16)
      ((rows29.drop 192).take 16) = true := by decide +kernel

private theorem gate27_block13 :
    check rows05 ((rows08.drop 208).take 16)
      ((rows29.drop 208).take 16) = true := by decide +kernel

private theorem gate27_block14 :
    check rows05 ((rows08.drop 224).take 16)
      ((rows29.drop 224).take 16) = true := by decide +kernel

private theorem gate27_block15 :
    check rows05 ((rows08.drop 240).take 16)
      ((rows29.drop 240).take 16) = true := by decide +kernel

private theorem gate27_block16 :
    check rows05 ((rows08.drop 256).take 16)
      ((rows29.drop 256).take 16) = true := by decide +kernel

private theorem gate27_block17 :
    check rows05 ((rows08.drop 272).take 16)
      ((rows29.drop 272).take 16) = true := by decide +kernel

private theorem gate27_block18 :
    check rows05 ((rows08.drop 288).take 16)
      ((rows29.drop 288).take 16) = true := by decide +kernel

private theorem gate27_block19 :
    check rows05 ((rows08.drop 304).take 16)
      ((rows29.drop 304).take 16) = true := by decide +kernel

private theorem gate27_block20 :
    check rows05 ((rows08.drop 320).take 16)
      ((rows29.drop 320).take 16) = true := by decide +kernel

private theorem gate27_block21 :
    check rows05 ((rows08.drop 336).take 16)
      ((rows29.drop 336).take 16) = true := by decide +kernel

private theorem gate27_block22 :
    check rows05 ((rows08.drop 352).take 16)
      ((rows29.drop 352).take 16) = true := by decide +kernel

private theorem gate27_block23 :
    check rows05 ((rows08.drop 368).take 16)
      ((rows29.drop 368).take 16) = true := by decide +kernel

private theorem gate27_block24 :
    check rows05 ((rows08.drop 384).take 16)
      ((rows29.drop 384).take 16) = true := by decide +kernel

private theorem gate27_block25 :
    check rows05 ((rows08.drop 400).take 16)
      ((rows29.drop 400).take 16) = true := by decide +kernel

private theorem gate27_block26 :
    check rows05 ((rows08.drop 416).take 16)
      ((rows29.drop 416).take 16) = true := by decide +kernel

private theorem gate27_block27 :
    check rows05 ((rows08.drop 432).take 16)
      ((rows29.drop 432).take 16) = true := by decide +kernel

private theorem gate27_block28 :
    check rows05 ((rows08.drop 448).take 16)
      ((rows29.drop 448).take 16) = true := by decide +kernel

private theorem gate27_block29 :
    check rows05 ((rows08.drop 464).take 16)
      ((rows29.drop 464).take 16) = true := by decide +kernel

private theorem gate27_block30 :
    check rows05 ((rows08.drop 480).take 16)
      ((rows29.drop 480).take 16) = true := by decide +kernel

private theorem gate27_block31 :
    check rows05 ((rows08.drop 496).take 16)
      ((rows29.drop 496).take 16) = true := by decide +kernel

private theorem gate27_block32 :
    check rows05 ((rows08.drop 512).take 16)
      ((rows29.drop 512).take 16) = true := by decide +kernel

private theorem gate27_block33 :
    check rows05 ((rows08.drop 528).take 16)
      ((rows29.drop 528).take 16) = true := by decide +kernel

private theorem gate27_block34 :
    check rows05 ((rows08.drop 544).take 16)
      ((rows29.drop 544).take 16) = true := by decide +kernel

private theorem gate27_block35 :
    check rows05 ((rows08.drop 560).take 16)
      ((rows29.drop 560).take 16) = true := by decide +kernel

private theorem gate27_block36 :
    check rows05 ((rows08.drop 576).take 16)
      ((rows29.drop 576).take 16) = true := by decide +kernel

private theorem gate27_block37 :
    check rows05 ((rows08.drop 592).take 16)
      ((rows29.drop 592).take 16) = true := by decide +kernel

private theorem gate27_block38 :
    check rows05 ((rows08.drop 608).take 16)
      ((rows29.drop 608).take 16) = true := by decide +kernel

private theorem gate27_block39 :
    check rows05 ((rows08.drop 624).take 16)
      ((rows29.drop 624).take 16) = true := by decide +kernel

private theorem gate27_block40 :
    check rows05 ((rows08.drop 640).take 16)
      ((rows29.drop 640).take 16) = true := by decide +kernel

private theorem gate27_block41 :
    check rows05 ((rows08.drop 656).take 16)
      ((rows29.drop 656).take 16) = true := by decide +kernel

private theorem gate27_block42 :
    check rows05 ((rows08.drop 672).take 16)
      ((rows29.drop 672).take 16) = true := by decide +kernel

private theorem gate27_block43 :
    check rows05 ((rows08.drop 688).take 16)
      ((rows29.drop 688).take 16) = true := by decide +kernel

private theorem gate27_block44 :
    check rows05 ((rows08.drop 704).take 16)
      ((rows29.drop 704).take 16) = true := by decide +kernel

private theorem gate27_block45 :
    check rows05 ((rows08.drop 720).take 16)
      ((rows29.drop 720).take 16) = true := by decide +kernel

private theorem gate27_block46 :
    check rows05 ((rows08.drop 736).take 16)
      ((rows29.drop 736).take 16) = true := by decide +kernel

private theorem gate27_block47 :
    check rows05 ((rows08.drop 752).take 16)
      ((rows29.drop 752).take 16) = true := by decide +kernel

private theorem gate27_block48 :
    check rows05 ((rows08.drop 768).take 16)
      ((rows29.drop 768).take 16) = true := by decide +kernel

private theorem gate27_block49 :
    check rows05 ((rows08.drop 784).take 16)
      ((rows29.drop 784).take 16) = true := by decide +kernel

private theorem gate27_block50 :
    check rows05 ((rows08.drop 800).take 16)
      ((rows29.drop 800).take 16) = true := by decide +kernel

private theorem gate27_block51 :
    check rows05 ((rows08.drop 816).take 16)
      ((rows29.drop 816).take 16) = true := by decide +kernel

private theorem gate27_block52 :
    check rows05 ((rows08.drop 832).take 16)
      ((rows29.drop 832).take 16) = true := by decide +kernel

private theorem gate27_block53 :
    check rows05 ((rows08.drop 848).take 16)
      ((rows29.drop 848).take 16) = true := by decide +kernel

private theorem gate27_block54 :
    check rows05 ((rows08.drop 864).take 16)
      ((rows29.drop 864).take 16) = true := by decide +kernel

private theorem gate27_block55 :
    check rows05 ((rows08.drop 880).take 16)
      ((rows29.drop 880).take 16) = true := by decide +kernel

private theorem gate27_blocks (b : Fin 56) :
    check rows05 ((rows08.drop (16*b.val)).take 16)
      ((rows29.drop (16*b.val)).take 16) = true := by
  fin_cases b
  · exact gate27_block00
  · exact gate27_block01
  · exact gate27_block02
  · exact gate27_block03
  · exact gate27_block04
  · exact gate27_block05
  · exact gate27_block06
  · exact gate27_block07
  · exact gate27_block08
  · exact gate27_block09
  · exact gate27_block10
  · exact gate27_block11
  · exact gate27_block12
  · exact gate27_block13
  · exact gate27_block14
  · exact gate27_block15
  · exact gate27_block16
  · exact gate27_block17
  · exact gate27_block18
  · exact gate27_block19
  · exact gate27_block20
  · exact gate27_block21
  · exact gate27_block22
  · exact gate27_block23
  · exact gate27_block24
  · exact gate27_block25
  · exact gate27_block26
  · exact gate27_block27
  · exact gate27_block28
  · exact gate27_block29
  · exact gate27_block30
  · exact gate27_block31
  · exact gate27_block32
  · exact gate27_block33
  · exact gate27_block34
  · exact gate27_block35
  · exact gate27_block36
  · exact gate27_block37
  · exact gate27_block38
  · exact gate27_block39
  · exact gate27_block40
  · exact gate27_block41
  · exact gate27_block42
  · exact gate27_block43
  · exact gate27_block44
  · exact gate27_block45
  · exact gate27_block46
  · exact gate27_block47
  · exact gate27_block48
  · exact gate27_block49
  · exact gate27_block50
  · exact gate27_block51
  · exact gate27_block52
  · exact gate27_block53
  · exact gate27_block54
  · exact gate27_block55

/-- The complete fixed product, certified on every row. -/
theorem product_27 : ProductCheck 27 := by
  apply productCheck_of_rows
  intro r
  exact block_sound rows08 rows05 rows29 16 (16*(r.val/16))
    (gate27_blocks ⟨r.val/16, by omega⟩) rows08_length r.val (by omega) (by omega) r.isLt

end Representation.HigmanSims.LargeModels.TracePair.Descent.MatrixRelations.LongWords.MiddleTwo.Lower
