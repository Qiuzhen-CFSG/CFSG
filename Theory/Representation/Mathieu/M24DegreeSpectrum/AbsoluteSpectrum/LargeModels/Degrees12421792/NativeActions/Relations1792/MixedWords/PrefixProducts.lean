module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixProducts.XProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixProducts.YProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixProducts.ZProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixProducts.UProduct
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixProducts.VProduct

/-!
# The five shared mixed-word prefix products

The kernel checks every row of X = AB, Y = XB, Z = XY, U = XZ and V = ZY.
The fixed input tables are connected to their base-2048 expansions by proved
equalities, and the sound checker converts the closed computations into full
matrix products. All matrices retain the original untransposed ATLAS convention.

These are precisely the five prefix premises of `mixed_cubes_of_products` and
the three prefix premises of `nested_fourth_of_products` in `MixedWords.Circuit`.
The two terminal branches and source assembly remain with their own consumers.
Source: ATLAS M24G1-P1; see `PrefixProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords

/-- The first shared prefix, on the literal untransposed generator matrices. -/
theorem prefix_x : Data1792.first * Data1792.second = Data.x :=
  PrefixProducts.checked_x

/-- The second shared prefix. -/
theorem prefix_y : Data.x * Data1792.second = Data.y :=
  PrefixProducts.checked_y

/-- The common base of the nested-power word. -/
theorem prefix_z : Data.x * Data.y = Data.z :=
  PrefixProducts.checked_z

/-- The first cubed word's base. -/
theorem prefix_u : Data.x * Data.z = Data.u :=
  PrefixProducts.checked_u

/-- The second cubed word's base. -/
theorem prefix_v : Data.z * Data.y = Data.v :=
  PrefixProducts.checked_v

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords
