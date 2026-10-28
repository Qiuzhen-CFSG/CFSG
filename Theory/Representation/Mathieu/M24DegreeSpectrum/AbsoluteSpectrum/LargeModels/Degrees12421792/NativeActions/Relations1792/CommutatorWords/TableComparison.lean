module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.XProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.YProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.WProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.PProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.VProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords.TableComparison.VTables

/-!
# Comparisons with both fixed commutator-word tables

Put X = AB and Y = AB². Five complete, checked products give X, Y, W = YX,
P = WX and V = YP. Associativity then identifies W and V with the exact
positive source words ABBAB and ABBABBABAB. The output rows are also checked
against the fixed tables in `CommutatorWords.Data`.

The calculations use the original untransposed matrices and do not use any
generator-order equation. The previously certified B² table is used only
through its actual multiplication theorem. Source: ATLAS M24G1-P1, positive
words 3 and 4; see `TableComparison/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
open Arithmetic GeneratorOrders TableComparison

private theorem x_eq : decodeRows 1792 xRows.flatten = Data1792.first * Data1792.second := by
  simpa only [firstRows_decode, secondRows_decode] using x_product.symm

private theorem y_eq : decodeRows 1792 yRows.flatten = Data1792.first * Data1792.second ^ 2 := by
  simpa only [firstRows_decode, ← secondSquare] using y_product.symm

/-- The fixed third-word candidate is exactly the original positive row word. -/
theorem wordThree_eq : Data1792.first * Data1792.second ^ 2 * Data1792.first *
    Data1792.second = Data.wordThree := by
  have h := w_product
  rw [y_eq, x_eq, wRows_decode] at h
  simpa only [mul_assoc] using h

/-- The fixed fourth-word candidate is exactly the original positive row word. -/
theorem wordFour_eq : Data1792.first * Data1792.second ^ 2 * Data1792.first *
    Data1792.second ^ 2 * Data1792.first * Data1792.second * Data1792.first *
    Data1792.second = Data.wordFour := by
  have hp := p_product
  rw [wRows_decode, ← wordThree_eq, x_eq] at hp
  have h := v_product
  rw [y_eq, ← hp, vRows_decode] at h
  simpa only [mul_assoc] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.CommutatorWords
