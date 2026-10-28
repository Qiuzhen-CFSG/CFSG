module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B00
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B01
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B02
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B03
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B04
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B05
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B06
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B07
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B08
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B09
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B10
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B11
public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table.RowChecks.B12

/-!
# Complete shared-row coverage

The 13 blocks of 9 batches of 24 rows cover all 2808 row indices. Both packed
right-generator products and the successor bounds are proved without any
packed-arithmetic correctness assumption. `Table` applies these facts to every
row of every determinant-one native matrix code.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table

private theorem allRowBlocks : ∀ b : Fin 13, ∀ q : Fin 9, ∀ i : Fin 24,
    RowGood ((b.val * 9 + q.val) * 24 + i.val) := by
  intro b
  fin_cases b
  · exact rowBlock0
  · exact rowBlock1
  · exact rowBlock2
  · exact rowBlock3
  · exact rowBlock4
  · exact rowBlock5
  · exact rowBlock6
  · exact rowBlock7
  · exact rowBlock8
  · exact rowBlock9
  · exact rowBlock10
  · exact rowBlock11
  · exact rowBlock12

theorem row_correct (n : ℕ) (hn : n < 2808) : RowGood n := by
  have hq : n / 24 < 117 := by omega
  have hb : n / 24 / 9 < 13 := Nat.div_lt_of_lt_mul hq
  have hrq : n / 24 % 9 < 9 := Nat.mod_lt _ (by decide)
  have hri : n % 24 < 24 := Nat.mod_lt _ (by decide)
  have h := allRowBlocks ⟨n / 24 / 9, hb⟩ ⟨n / 24 % 9, hrq⟩ ⟨n % 24, hri⟩
  have heq : (n / 24 / 9 * 9 + n / 24 % 9) * 24 + n % 24 = n := by omega
  simpa only [heq] using h

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.NativeAction.Packed.Table
