module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.GeneratorOrders.FirstSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.GeneratorOrders.SecondSquare
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.GeneratorOrders.SecondCube

/-!
# The square and cube of the literal degree-1242 ATLAS generators

Bounded, kernel-checked row certificates prove the first generator's square,
the second generator's square, and the product of that square with the second
generator. The tables are connected to the unchanged, untransposed matrices.
Thus the first two words of M24G1-P1 hold without representation, presentation,
or numerical-certificate premises.

Source: ATLAS M24G1-P1 and M24G1-f2r1242B0.m1/.m2. See
`GeneratorOrders/source/README.md` for provenance and check measurements.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
open Thompson.BinaryMatrix

/-- The first source word on the literal untransposed ATLAS matrix. -/
theorem first_square : Data1242.first ^ 2 = 1 := by
  have h := GeneratorOrders.FirstSquareProduct
  rw [GeneratorOrders.aRows_array, GeneratorOrders.iaRows_identity,
    GeneratorOrders.decode_range_identity] at h
  simpa only [pow_two, Data1242.first] using h

/-- The second source word on the literal untransposed ATLAS matrix. -/
theorem second_cube : Data1242.second ^ 3 = 1 := by
  have hs := GeneratorOrders.SecondSquareProduct
  rw [GeneratorOrders.bRows_array] at hs
  have hc := GeneratorOrders.SecondCubeProduct
  rw [GeneratorOrders.bRows_array, GeneratorOrders.ibRows_identity,
    GeneratorOrders.decode_range_identity] at hc
  change Data1242.second * Data1242.second = _ at hs
  change decode 1242 GeneratorOrders.cRows.toArray * Data1242.second = 1 at hc
  rw [show (3 : Nat) = 2 + 1 from rfl, pow_succ, pow_two, hs, hc]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242
