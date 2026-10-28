module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B00
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B01
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B02
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B03
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B04
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B05
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B06
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B07
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B08
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B09
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B10
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B11
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B12
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B13
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B14
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B15
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B16
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B17
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B18
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B19
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B20
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B21
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B22
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B23
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B24
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B25
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.NativeChecks.B26

/-!
# Complete coverage of the literal native matrix codes

The 27 blocks of 9 batches of 81 codes exhaust all 3⁹ native codes. Each batch
checks the determinant guard and both actual right-generator edges, together
with source-row bounds. Thus no generation or presentation assumption replaces
coverage. `Table` turns these scalar certificates into the requested matrix
certificate using `Slots` and the independently checked shared rows.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

private theorem allNativeBlocks : ∀ b : Fin 27, ∀ q : Fin 9, ∀ r : Fin 81,
    NativeGood ⟨(b.val * 9 + q.val) * 81 + r.val, by omega⟩ := by
  intro b
  fin_cases b
  · exact nativeBlock0
  · exact nativeBlock1
  · exact nativeBlock2
  · exact nativeBlock3
  · exact nativeBlock4
  · exact nativeBlock5
  · exact nativeBlock6
  · exact nativeBlock7
  · exact nativeBlock8
  · exact nativeBlock9
  · exact nativeBlock10
  · exact nativeBlock11
  · exact nativeBlock12
  · exact nativeBlock13
  · exact nativeBlock14
  · exact nativeBlock15
  · exact nativeBlock16
  · exact nativeBlock17
  · exact nativeBlock18
  · exact nativeBlock19
  · exact nativeBlock20
  · exact nativeBlock21
  · exact nativeBlock22
  · exact nativeBlock23
  · exact nativeBlock24
  · exact nativeBlock25
  · exact nativeBlock26

theorem native_correct (c : Matrix.PSL3Three.MatrixCode) : NativeGood c := by
  have hq : c.val / 81 < 243 := by omega
  have hb : c.val / 81 / 9 < 27 := Nat.div_lt_of_lt_mul hq
  have hrq : c.val / 81 % 9 < 9 := Nat.mod_lt _ (by decide)
  have hri : c.val % 81 < 81 := Nat.mod_lt _ (by decide)
  have h := allNativeBlocks ⟨c.val / 81 / 9, hb⟩ ⟨c.val / 81 % 9, hrq⟩ ⟨c.val % 81, hri⟩
  have heq : (⟨(c.val / 81 / 9 * 9 + c.val / 81 % 9) * 81 + c.val % 81, by omega⟩ :
      Matrix.PSL3Three.MatrixCode) = c := by
    apply Fin.ext
    dsimp
    omega
  simpa only [heq] using h

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
