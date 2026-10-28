module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders.Checker

/-!
# Balanced widening checks for the fixed V table

The existing balanced conversion skips zero subblocks. Its proved equality
with the original expansion converts every numerical check to the exact
`expandBlocks 32 56` interface consumed by the cube products.

Source: ATLAS M24G1-P1; see `../../source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.VChecks
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.Arithmetic
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.GeneratorOrders

/-- A balanced check proves the original widening equation, with every row retained. -/
theorem widening (xs ys : List Nat)
    (h : xs = ys.map (expandTree 6 1792)) :
    xs = ys.map (expandBlocks 32 56) := by
  have he : expandTree 6 1792 = expandBlocks 32 56 := by
    funext a
    rw [expandTree_eq, expandBlocks_eq]
  simpa only [he] using h

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeProducts.VChecks
