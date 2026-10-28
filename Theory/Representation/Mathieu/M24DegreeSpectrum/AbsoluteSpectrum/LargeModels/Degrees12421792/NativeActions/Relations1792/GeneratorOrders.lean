module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.FirstSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.SecondCube

/-!
# The first two exact degree-1792 ATLAS relations

The literal untransposed generators have square and cube equal to the identity.
Every binary-row bridge, radix expansion, and product certificate is checked by
Lean's kernel. No native action, density, or presentation-exactness premise is used.
Source: M24G1-P1 and M24G1-f2r1792B0.m1/.m2; see
`GeneratorOrders/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792

namespace GeneratorOrders
open Arithmetic

/-- Packed first-generator input in the exact existing chunk-checker convention. -/
theorem firstWide_original : firstWide.flatten =
    Data1792.firstRows.toList.map (expandBlocks 32 56) := by
  have hf : expandBlocks 32 56 = expand 1792 := funext (expandBlocks_eq 32 56)
  rw [firstWide_eq, firstRows_eq, hf]

/-- Packed second-generator input in the exact existing chunk-checker convention. -/
theorem secondWide_original : secondWide.flatten =
    Data1792.secondRows.toList.map (expandBlocks 32 56) := by
  have hf : expandBlocks 32 56 = expand 1792 := funext (expandBlocks_eq 32 56)
  rw [secondWide_eq, secondRows_eq, hf]

end GeneratorOrders

/-- First exact positive ATLAS M24G1-P1 equation. -/
theorem first_square : Data1792.first ^ 2 = 1 := GeneratorOrders.firstSquare

/-- Second exact positive ATLAS M24G1-P1 equation. -/
theorem second_cube : Data1792.second ^ 3 = 1 := GeneratorOrders.secondCube

/-- Application to the literal first presentation word. -/
theorem first_word : Presentation.rowRelatorValues Data1792.first Data1792.second 0 = 1 := by
  simpa only [Presentation.rowRelatorValues, Matrix.cons_val_zero] using first_square

/-- Application to the literal second presentation word. -/
theorem second_word : Presentation.rowRelatorValues Data1792.first Data1792.second 1 = 1 := by
  change Data1792.second ^ 3 = 1
  exact second_cube

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792
