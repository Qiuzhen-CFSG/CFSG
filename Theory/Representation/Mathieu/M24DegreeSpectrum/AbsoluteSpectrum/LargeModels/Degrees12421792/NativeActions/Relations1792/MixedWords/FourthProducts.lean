module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.Representative
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.ZProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TProducts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts.TerminalProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthData

/-!
# The five complete products for the nested fourth-power branch

The three certificate families prove every row of the five literal products,
including all bridges from the widened tables to the original candidate rows.
The unconditional equations below discharge exactly the five terminal matrix
premises of `nested_fourth_of_products`. The numerical adapters remain public.
Identification of the shared prefixes with generator words belongs to the
source-word assembly. Source: ATLAS M24G1-P1; see `FourthProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts

/-- Apply a complete numerical certificate to the literal z · z product. -/
theorem z_square_of_rows (wide : List (List Nat))
    (hw : wide.flatten = Data.zRows.map (Arithmetic.expandFast 448))
    (hl : ∀ b ∈ wide, b.length = 32)
    (h : Data.zRows.map (fun a => Arithmetic.row a wide) = Data.z2Rows) :
    Data.z * Data.z = Data.z2 := by
  exact Arithmetic.product Data.zRows Data.zRows Data.z2Rows wide
    Data.zRows_length Data.zRows_length hw hl h

/-- Apply a complete numerical certificate to the literal z2 · z product. -/
theorem z_cube_of_rows (wide : List (List Nat))
    (hw : wide.flatten = Data.zRows.map (Arithmetic.expandFast 448))
    (hl : ∀ b ∈ wide, b.length = 32)
    (h : Data.z2Rows.map (fun a => Arithmetic.row a wide) = Data.z3Rows) :
    Data.z2 * Data.z = Data.z3 := by
  exact Arithmetic.product Data.z2Rows Data.zRows Data.z3Rows wide
    Data.z2Rows_length Data.zRows_length hw hl h

/-- Apply a complete numerical certificate to the literal x · z3 product. -/
theorem t_product_of_rows (wide : List (List Nat))
    (hw : wide.flatten = Data.z3Rows.map (Arithmetic.expandFast 448))
    (hl : ∀ b ∈ wide, b.length = 32)
    (h : Data.xRows.map (fun a => Arithmetic.row a wide) = Data.tRows) :
    Data.x * Data.z3 = Data.t := by
  exact Arithmetic.product Data.xRows Data.z3Rows Data.tRows wide
    Data.xRows_length Data.z3Rows_length hw hl h

/-- Apply a complete numerical certificate to the literal t · t product. -/
theorem t_square_of_rows (wide : List (List Nat))
    (hw : wide.flatten = Data.tRows.map (Arithmetic.expandFast 448))
    (hl : ∀ b ∈ wide, b.length = 32)
    (h : Data.tRows.map (fun a => Arithmetic.row a wide) = Data.t2Rows) :
    Data.t * Data.t = Data.t2 := by
  exact Arithmetic.product Data.tRows Data.tRows Data.t2Rows wide
    Data.tRows_length Data.tRows_length hw hl h

/-- The entire terminal widening has already been certified. -/
theorem t_fourth_of_rows
    (h : Data.t2Rows.map (fun a => Arithmetic.row a WideT2.blocks) =
      (List.range 1792).map (fun i => 2^i)) : Data.t2 * Data.t2 = 1 := by
  have hp := Arithmetic.product Data.t2Rows Data.t2Rows
    ((List.range 1792).map (fun i => 2^i)) WideT2.blocks
    Data.t2Rows_length Data.t2Rows_length WideT2.bridge WideT2.blocks_lengths h
  exact hp.trans (Arithmetic.decode_identity 1792)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthProducts

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords

/-- The square of the literal Z table, discharging `hz2` in the fourth-power circuit. -/
theorem z_square : Data.z * Data.z = Data.z2 :=
  FourthProducts.ZProducts.z_square

/-- The cube step for the literal Z table, discharging `hz3` in the circuit. -/
theorem z_cube : Data.z2 * Data.z = Data.z3 :=
  FourthProducts.ZProducts.z_cube

/-- The literal X · Z3 product, discharging `ht` in the fourth-power circuit. -/
theorem t_product : Data.x * Data.z3 = Data.t :=
  FourthProducts.TProducts.t_product

/-- The square of the literal T table, discharging `ht2` in the circuit. -/
theorem t_square : Data.t * Data.t = Data.t2 :=
  FourthProducts.TProducts.t_square

/-- The terminal T2 square, discharging `hsq` in the fourth-power circuit. -/
theorem t_fourth : Data.t2 * Data.t2 = 1 :=
  FourthProducts.TerminalProduct.t_fourth

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords
