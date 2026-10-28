module

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block00

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block01

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block02

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block03

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block04

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block05

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block06

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block07

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block08

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block09

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block10

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block11

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block12

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block13

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block14

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block15

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block16

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block17

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block18

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block19

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block20

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block21

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block22

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block23

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block24

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block25

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block26

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block27

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block28

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block29

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block30

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block31

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block32

public import Theory.Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank.Block33

/-!
# Interpretation and assembly of the checked HS pivot blocks

The extraction proof identifies the packed matrix with the actual minor of
`Sum.elim kernelMatrix liftMatrix`, flattened with the kernel rows first.
The multiplication proof assembles the checked 16-row blocks and uses the
rectangular multiplication soundness theorem. No inverse is chosen abstractly.
Source: `Binary/source/section518.json`, with attribution in `Rank/Blocks.lean`.
-/

public section

namespace Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank

open RowArithmetic Thompson.BinaryMatrix

private theorem gather_suffix34 : sourceSuffix34.map (gather runs) = minorSuffix34 := rfl

private theorem gather_suffix33 : sourceSuffix33.map (gather runs) = minorSuffix33 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock33) (l₂ := sourceSuffix34)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block33 gather_suffix34)

private theorem gather_suffix32 : sourceSuffix32.map (gather runs) = minorSuffix32 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock32) (l₂ := sourceSuffix33)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block32 gather_suffix33)

private theorem gather_suffix31 : sourceSuffix31.map (gather runs) = minorSuffix31 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock31) (l₂ := sourceSuffix32)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block31 gather_suffix32)

private theorem gather_suffix30 : sourceSuffix30.map (gather runs) = minorSuffix30 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock30) (l₂ := sourceSuffix31)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block30 gather_suffix31)

private theorem gather_suffix29 : sourceSuffix29.map (gather runs) = minorSuffix29 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock29) (l₂ := sourceSuffix30)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block29 gather_suffix30)

private theorem gather_suffix28 : sourceSuffix28.map (gather runs) = minorSuffix28 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock28) (l₂ := sourceSuffix29)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block28 gather_suffix29)

private theorem gather_suffix27 : sourceSuffix27.map (gather runs) = minorSuffix27 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock27) (l₂ := sourceSuffix28)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block27 gather_suffix28)

private theorem gather_suffix26 : sourceSuffix26.map (gather runs) = minorSuffix26 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock26) (l₂ := sourceSuffix27)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block26 gather_suffix27)

private theorem gather_suffix25 : sourceSuffix25.map (gather runs) = minorSuffix25 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock25) (l₂ := sourceSuffix26)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block25 gather_suffix26)

private theorem gather_suffix24 : sourceSuffix24.map (gather runs) = minorSuffix24 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock24) (l₂ := sourceSuffix25)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block24 gather_suffix25)

private theorem gather_suffix23 : sourceSuffix23.map (gather runs) = minorSuffix23 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock23) (l₂ := sourceSuffix24)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block23 gather_suffix24)

private theorem gather_suffix22 : sourceSuffix22.map (gather runs) = minorSuffix22 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock22) (l₂ := sourceSuffix23)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block22 gather_suffix23)

private theorem gather_suffix21 : sourceSuffix21.map (gather runs) = minorSuffix21 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock21) (l₂ := sourceSuffix22)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block21 gather_suffix22)

private theorem gather_suffix20 : sourceSuffix20.map (gather runs) = minorSuffix20 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock20) (l₂ := sourceSuffix21)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block20 gather_suffix21)

private theorem gather_suffix19 : sourceSuffix19.map (gather runs) = minorSuffix19 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock19) (l₂ := sourceSuffix20)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block19 gather_suffix20)

private theorem gather_suffix18 : sourceSuffix18.map (gather runs) = minorSuffix18 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock18) (l₂ := sourceSuffix19)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block18 gather_suffix19)

private theorem gather_suffix17 : sourceSuffix17.map (gather runs) = minorSuffix17 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock17) (l₂ := sourceSuffix18)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block17 gather_suffix18)

private theorem gather_suffix16 : sourceSuffix16.map (gather runs) = minorSuffix16 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock16) (l₂ := sourceSuffix17)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block16 gather_suffix17)

private theorem gather_suffix15 : sourceSuffix15.map (gather runs) = minorSuffix15 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock15) (l₂ := sourceSuffix16)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block15 gather_suffix16)

private theorem gather_suffix14 : sourceSuffix14.map (gather runs) = minorSuffix14 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock14) (l₂ := sourceSuffix15)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block14 gather_suffix15)

private theorem gather_suffix13 : sourceSuffix13.map (gather runs) = minorSuffix13 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock13) (l₂ := sourceSuffix14)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block13 gather_suffix14)

private theorem gather_suffix12 : sourceSuffix12.map (gather runs) = minorSuffix12 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock12) (l₂ := sourceSuffix13)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block12 gather_suffix13)

private theorem gather_suffix11 : sourceSuffix11.map (gather runs) = minorSuffix11 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock11) (l₂ := sourceSuffix12)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block11 gather_suffix12)

private theorem gather_suffix10 : sourceSuffix10.map (gather runs) = minorSuffix10 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock10) (l₂ := sourceSuffix11)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block10 gather_suffix11)

private theorem gather_suffix9 : sourceSuffix9.map (gather runs) = minorSuffix9 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock9) (l₂ := sourceSuffix10)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block9 gather_suffix10)

private theorem gather_suffix8 : sourceSuffix8.map (gather runs) = minorSuffix8 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock8) (l₂ := sourceSuffix9)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block8 gather_suffix9)

private theorem gather_suffix7 : sourceSuffix7.map (gather runs) = minorSuffix7 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock7) (l₂ := sourceSuffix8)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block7 gather_suffix8)

private theorem gather_suffix6 : sourceSuffix6.map (gather runs) = minorSuffix6 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock6) (l₂ := sourceSuffix7)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block6 gather_suffix7)

private theorem gather_suffix5 : sourceSuffix5.map (gather runs) = minorSuffix5 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock5) (l₂ := sourceSuffix6)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block5 gather_suffix6)

private theorem gather_suffix4 : sourceSuffix4.map (gather runs) = minorSuffix4 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock4) (l₂ := sourceSuffix5)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block4 gather_suffix5)

private theorem gather_suffix3 : sourceSuffix3.map (gather runs) = minorSuffix3 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock3) (l₂ := sourceSuffix4)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block3 gather_suffix4)

private theorem gather_suffix2 : sourceSuffix2.map (gather runs) = minorSuffix2 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock2) (l₂ := sourceSuffix3)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block2 gather_suffix3)

private theorem gather_suffix1 : sourceSuffix1.map (gather runs) = minorSuffix1 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock1) (l₂ := sourceSuffix2)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block1 gather_suffix2)

private theorem gather_suffix0 : sourceSuffix0.map (gather runs) = minorSuffix0 := by
  exact (List.map_append (f := gather runs) (l₁ := sourceBlock0) (l₂ := sourceSuffix1)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) gather_block0 gather_suffix1)

theorem gather_rows : sourceSuffix0.map (gather runs) = minorSuffix0 := gather_suffix0

private theorem product_suffix34 : minorSuffix34.map (combine pivotInverseRows) = oneSuffix34 := rfl

private theorem product_suffix33 : minorSuffix33.map (combine pivotInverseRows) = oneSuffix33 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock33) (l₂ := minorSuffix34)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block33 product_suffix34)

private theorem product_suffix32 : minorSuffix32.map (combine pivotInverseRows) = oneSuffix32 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock32) (l₂ := minorSuffix33)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block32 product_suffix33)

private theorem product_suffix31 : minorSuffix31.map (combine pivotInverseRows) = oneSuffix31 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock31) (l₂ := minorSuffix32)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block31 product_suffix32)

private theorem product_suffix30 : minorSuffix30.map (combine pivotInverseRows) = oneSuffix30 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock30) (l₂ := minorSuffix31)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block30 product_suffix31)

private theorem product_suffix29 : minorSuffix29.map (combine pivotInverseRows) = oneSuffix29 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock29) (l₂ := minorSuffix30)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block29 product_suffix30)

private theorem product_suffix28 : minorSuffix28.map (combine pivotInverseRows) = oneSuffix28 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock28) (l₂ := minorSuffix29)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block28 product_suffix29)

private theorem product_suffix27 : minorSuffix27.map (combine pivotInverseRows) = oneSuffix27 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock27) (l₂ := minorSuffix28)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block27 product_suffix28)

private theorem product_suffix26 : minorSuffix26.map (combine pivotInverseRows) = oneSuffix26 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock26) (l₂ := minorSuffix27)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block26 product_suffix27)

private theorem product_suffix25 : minorSuffix25.map (combine pivotInverseRows) = oneSuffix25 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock25) (l₂ := minorSuffix26)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block25 product_suffix26)

private theorem product_suffix24 : minorSuffix24.map (combine pivotInverseRows) = oneSuffix24 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock24) (l₂ := minorSuffix25)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block24 product_suffix25)

private theorem product_suffix23 : minorSuffix23.map (combine pivotInverseRows) = oneSuffix23 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock23) (l₂ := minorSuffix24)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block23 product_suffix24)

private theorem product_suffix22 : minorSuffix22.map (combine pivotInverseRows) = oneSuffix22 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock22) (l₂ := minorSuffix23)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block22 product_suffix23)

private theorem product_suffix21 : minorSuffix21.map (combine pivotInverseRows) = oneSuffix21 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock21) (l₂ := minorSuffix22)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block21 product_suffix22)

private theorem product_suffix20 : minorSuffix20.map (combine pivotInverseRows) = oneSuffix20 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock20) (l₂ := minorSuffix21)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block20 product_suffix21)

private theorem product_suffix19 : minorSuffix19.map (combine pivotInverseRows) = oneSuffix19 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock19) (l₂ := minorSuffix20)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block19 product_suffix20)

private theorem product_suffix18 : minorSuffix18.map (combine pivotInverseRows) = oneSuffix18 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock18) (l₂ := minorSuffix19)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block18 product_suffix19)

private theorem product_suffix17 : minorSuffix17.map (combine pivotInverseRows) = oneSuffix17 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock17) (l₂ := minorSuffix18)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block17 product_suffix18)

private theorem product_suffix16 : minorSuffix16.map (combine pivotInverseRows) = oneSuffix16 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock16) (l₂ := minorSuffix17)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block16 product_suffix17)

private theorem product_suffix15 : minorSuffix15.map (combine pivotInverseRows) = oneSuffix15 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock15) (l₂ := minorSuffix16)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block15 product_suffix16)

private theorem product_suffix14 : minorSuffix14.map (combine pivotInverseRows) = oneSuffix14 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock14) (l₂ := minorSuffix15)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block14 product_suffix15)

private theorem product_suffix13 : minorSuffix13.map (combine pivotInverseRows) = oneSuffix13 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock13) (l₂ := minorSuffix14)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block13 product_suffix14)

private theorem product_suffix12 : minorSuffix12.map (combine pivotInverseRows) = oneSuffix12 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock12) (l₂ := minorSuffix13)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block12 product_suffix13)

private theorem product_suffix11 : minorSuffix11.map (combine pivotInverseRows) = oneSuffix11 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock11) (l₂ := minorSuffix12)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block11 product_suffix12)

private theorem product_suffix10 : minorSuffix10.map (combine pivotInverseRows) = oneSuffix10 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock10) (l₂ := minorSuffix11)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block10 product_suffix11)

private theorem product_suffix9 : minorSuffix9.map (combine pivotInverseRows) = oneSuffix9 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock9) (l₂ := minorSuffix10)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block9 product_suffix10)

private theorem product_suffix8 : minorSuffix8.map (combine pivotInverseRows) = oneSuffix8 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock8) (l₂ := minorSuffix9)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block8 product_suffix9)

private theorem product_suffix7 : minorSuffix7.map (combine pivotInverseRows) = oneSuffix7 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock7) (l₂ := minorSuffix8)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block7 product_suffix8)

private theorem product_suffix6 : minorSuffix6.map (combine pivotInverseRows) = oneSuffix6 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock6) (l₂ := minorSuffix7)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block6 product_suffix7)

private theorem product_suffix5 : minorSuffix5.map (combine pivotInverseRows) = oneSuffix5 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock5) (l₂ := minorSuffix6)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block5 product_suffix6)

private theorem product_suffix4 : minorSuffix4.map (combine pivotInverseRows) = oneSuffix4 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock4) (l₂ := minorSuffix5)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block4 product_suffix5)

private theorem product_suffix3 : minorSuffix3.map (combine pivotInverseRows) = oneSuffix3 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock3) (l₂ := minorSuffix4)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block3 product_suffix4)

private theorem product_suffix2 : minorSuffix2.map (combine pivotInverseRows) = oneSuffix2 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock2) (l₂ := minorSuffix3)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block2 product_suffix3)

private theorem product_suffix1 : minorSuffix1.map (combine pivotInverseRows) = oneSuffix1 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock1) (l₂ := minorSuffix2)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block1 product_suffix2)

private theorem product_suffix0 : minorSuffix0.map (combine pivotInverseRows) = oneSuffix0 := by
  exact (List.map_append (f := combine pivotInverseRows) (l₁ := minorBlock0) (l₂ := minorSuffix1)).trans
    (congrArg₂ (fun xs ys : List ℕ => xs ++ ys) product_block0 product_suffix1)

theorem product_rows : minorSuffix0.map (combine pivotInverseRows) = oneSuffix0 := product_suffix0

/-- The packed rows are the literal shared minor in the saved pivot order. -/
theorem pivotMinor_eq : pivotMinor = matrix 539 539 minorSuffix0 := by
  funext i j
  change basisMatrix i (pivotColumn j) = bit minorSuffix0[i.val]! j.val
  rw [basisMatrix_eq]
  change bit (kernelRows ++ liftRows)[i.val]! (pivotColumn j).val = _
  rw [← source_alignment, ← map_entry sourceSuffix0 minorSuffix0 (gather runs)
    gather_rows 539 source_length i]
  simp only [bit, testBit_gather runs _ j.val (by rw [runs_width]; exact j.isLt), columns_eq]

/-- The saved inverse multiplies the checked packed minor to the identity. -/
theorem packed_product : matrix 539 539 minorSuffix0 * pivotInverse = 1 := by
  have hm := matrix_product 539 539 539 minorSuffix0 pivotInverseRows oneSuffix0
    inverse_length (map_entry minorSuffix0 oneSuffix0 (combine pivotInverseRows)
      product_rows 539 minor_length)
  change matrix 539 539 minorSuffix0 * matrix 539 539 pivotInverseRows = _
  rw [hm]
  funext i j
  change bit oneSuffix0[i.val]! j.val = _
  rw [one_entry]
  simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]


end Representation.HigmanSims.LargeModels.Binary.Large.Tensor518.Rank
