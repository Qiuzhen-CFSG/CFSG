module
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.RootModel.ReferenceCentralizer.Volume.BlockImage.IntegralAlignment.WordCoordinates

/-!
# Kernel certificates for the eight-factor integral word

Separate private identities bound the heartbeat cost of each integer product.
The final certificate assembles them without repeating arithmetic. The matrices
and their attribution are retained in WordData; Word applies these equations to
actual integral Leech isometries.
-/

set_option Elab.async false
@[expose] public section
open Matrix Atlas.Lattices
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
open scoped Long
open Long.Block.Realization
namespace IntegralAlignment
open WordData

private theorem product_2 : aNumerator * yNumerator = (2 : ℤ) • stage2 := by decide +kernel

private theorem product_3 : bNumerator * stage2 = (2 : ℤ) • stage3 := by decide +kernel

private theorem product_4 : aNumerator * stage3 = (2 : ℤ) • stage4 := by decide +kernel

private theorem product_5 : yNumerator * stage4 = (2 : ℤ) • stage5 := by decide +kernel

private theorem product_6 : bNumerator * stage5 = (2 : ℤ) • stage6 := by decide +kernel

private theorem product_7 : xNumerator * stage6 = (2 : ℤ) • stage7 := by decide +kernel

private theorem product_8 : yNumerator * stage7 = (2 : ℤ) • stage8 := by decide +kernel

private theorem product_9 : referenceNumerator * stage8 = stage8 * omegaNumerator := by decide +kernel

/-- Each word prefix and the final cubic intertwining, with denominators cleared. -/
theorem word_certificates :
    aNumerator * yNumerator = (2 : ℤ) • stage2 ∧
    bNumerator * stage2 = (2 : ℤ) • stage3 ∧
    aNumerator * stage3 = (2 : ℤ) • stage4 ∧
    yNumerator * stage4 = (2 : ℤ) • stage5 ∧
    bNumerator * stage5 = (2 : ℤ) • stage6 ∧
    xNumerator * stage6 = (2 : ℤ) • stage7 ∧
    yNumerator * stage7 = (2 : ℤ) • stage8 ∧
    referenceNumerator * stage8 = stage8 * omegaNumerator := by
  exact ⟨product_2, product_3, product_4, product_5, product_6, product_7, product_8, product_9⟩

end IntegralAlignment
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.RootModel
