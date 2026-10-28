module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.XMulB
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.YMulX
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.YMulW
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts.ZMulX
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.Circuit

/-!
# The degree-1242 commutator prefixes

Four fixed numerical products are proved in the descendants using the existing
verified row checker. The exact source-word comparisons from `Circuit` then
identify the two positive words with their literal output matrices, without
any order or presentation hypotheses.

Source: ATLAS M24G1-P1 and the untransposed M24G1-f2r1242B0.m1/.m2 arrays;
see `source/README.md`. Certificate structure and measured checks are recorded
in `PrefixProducts/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts

/-- The first positive source word has its checked literal output. -/
theorem wordThree :
    Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second = Data.w.matrix :=
  CommutatorWords.wordThree_eq x_mul_b y_mul_x

/-- The second positive source word has its checked literal output. -/
theorem wordFour :
    Data1242.first * Data1242.second^2 * Data1242.first * Data1242.second^2 *
      Data1242.first * Data1242.second * Data1242.first * Data1242.second = Data.v.matrix :=
  CommutatorWords.wordFour_eq x_mul_b y_mul_x y_mul_w z_mul_x

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1242.CommutatorWords.PrefixProducts
