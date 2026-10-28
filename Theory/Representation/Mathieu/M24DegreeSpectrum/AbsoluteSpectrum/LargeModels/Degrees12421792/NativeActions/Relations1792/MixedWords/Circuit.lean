module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.PrefixData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.CubeData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords.FourthData
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Data1792

/-!
# Product circuit for the two mixed ATLAS words

Put X = AB, Y = XB, Z = XY, U = XZ and V = ZY. The first target is
U³V³ = 1; the second is (XZ³)⁴ = 1. Shared prefixes and the two terminal
branches can be certified independently on the fixed candidate matrices.
This module proves the assembly, with every missing matrix product explicit.
It does not assert that any candidate is a product of the source generators.

The original untransposed row order is retained throughout. The final two
applications are exactly clauses 5 and 6 of `Presentation.rowRelatorValues`.
Source: John Bray's ATLAS M24G1-P1; see `source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords

private theorem prefixes
    (hx : Data1792.first * Data1792.second = Data.x)
    (hy : Data.x * Data1792.second = Data.y)
    (hz : Data.x * Data.y = Data.z) :
    Data.y = Data1792.first * Data1792.second ^ 2 ∧
    Data.z = Data1792.first * Data1792.second * Data1792.first * Data1792.second ^ 2 := by
  have hy' : Data.y = Data1792.first * Data1792.second ^ 2 := by
    rw [← hy, ← hx, pow_two, mul_assoc]
  refine ⟨hy', ?_⟩
  rw [← hz, ← hx, hy']
  simp only [mul_assoc]

/-- Assemble the first mixed word from five prefix and five cube products.
All ten hypotheses still require independent matrix certificates. -/
theorem mixed_cubes_of_products
    (hx : Data1792.first * Data1792.second = Data.x)
    (hy : Data.x * Data1792.second = Data.y)
    (hz : Data.x * Data.y = Data.z)
    (hu : Data.x * Data.z = Data.u)
    (hv : Data.z * Data.y = Data.v)
    (hu2 : Data.u * Data.u = Data.u2)
    (hu3 : Data.u2 * Data.u = Data.u3)
    (hv2 : Data.v * Data.v = Data.v2)
    (hv3 : Data.v2 * Data.v = Data.v3)
    (hinv : Data.u3 * Data.v3 = 1) :
    (Data1792.first * Data1792.second * Data1792.first * Data1792.second *
        Data1792.first * Data1792.second ^ 2) ^ 3 *
      (Data1792.first * Data1792.second * Data1792.first * Data1792.second ^ 2 *
        Data1792.first * Data1792.second ^ 2) ^ 3 = 1 := by
  obtain ⟨hy', hz'⟩ := prefixes hx hy hz
  have hu' : Data.u = Data1792.first * Data1792.second * Data1792.first *
      Data1792.second * Data1792.first * Data1792.second ^ 2 := by
    rw [← hu, ← hx, hz']
    simp only [mul_assoc]
  have hv' : Data.v = Data1792.first * Data1792.second * Data1792.first *
      Data1792.second ^ 2 * Data1792.first * Data1792.second ^ 2 := by
    rw [← hv, hz', hy']
    simp only [mul_assoc]
  have huPow : Data.u ^ 3 = Data.u3 := by rw [pow_succ, pow_two, hu2, hu3]
  have hvPow : Data.v ^ 3 = Data.v3 := by rw [pow_succ, pow_two, hv2, hv3]
  rw [← hu', ← hv', huPow, hvPow]
  exact hinv

/-- Assemble the nested word from three shared prefixes and five further
products. No generator-order or native-action assumption is used. -/
theorem nested_fourth_of_products
    (hx : Data1792.first * Data1792.second = Data.x)
    (hy : Data.x * Data1792.second = Data.y)
    (hz : Data.x * Data.y = Data.z)
    (hz2 : Data.z * Data.z = Data.z2)
    (hz3 : Data.z2 * Data.z = Data.z3)
    (ht : Data.x * Data.z3 = Data.t)
    (ht2 : Data.t * Data.t = Data.t2)
    (hsq : Data.t2 * Data.t2 = 1) :
    (Data1792.first * Data1792.second *
      (Data1792.first * Data1792.second * Data1792.first * Data1792.second ^ 2) ^ 3) ^ 4 = 1 := by
  have hz' := (prefixes hx hy hz).2
  have hbase : Data1792.first * Data1792.second *
      (Data1792.first * Data1792.second * Data1792.first * Data1792.second ^ 2) ^ 3 =
      Data.t := by
    rw [← hz', hx, pow_succ, pow_two, hz2, hz3, ht]
  have htPow : Data.t ^ 2 = Data.t2 := by rw [pow_two, ht2]
  rw [hbase, show 4 = 2 * 2 from rfl, pow_mul, htPow, pow_two]
  exact hsq

/-- Literal application to source clause 5. This is conditional on all ten
product checks, not a proof of the unconditional source relation. -/
theorem fifth_word_of_products
    (hx : Data1792.first * Data1792.second = Data.x)
    (hy : Data.x * Data1792.second = Data.y)
    (hz : Data.x * Data.y = Data.z)
    (hu : Data.x * Data.z = Data.u)
    (hv : Data.z * Data.y = Data.v)
    (hu2 : Data.u * Data.u = Data.u2)
    (hu3 : Data.u2 * Data.u = Data.u3)
    (hv2 : Data.v * Data.v = Data.v2)
    (hv3 : Data.v2 * Data.v = Data.v3)
    (hinv : Data.u3 * Data.v3 = 1) :
    Presentation.rowRelatorValues Data1792.first Data1792.second 5 = 1 := by
  exact mixed_cubes_of_products hx hy hz hu hv hu2 hu3 hv2 hv3 hinv

/-- Literal application to source clause 6, with its eight product checks
still explicit. -/
theorem sixth_word_of_products
    (hx : Data1792.first * Data1792.second = Data.x)
    (hy : Data.x * Data1792.second = Data.y)
    (hz : Data.x * Data.y = Data.z)
    (hz2 : Data.z * Data.z = Data.z2)
    (hz3 : Data.z2 * Data.z = Data.z3)
    (ht : Data.x * Data.z3 = Data.t)
    (ht2 : Data.t * Data.t = Data.t2)
    (hsq : Data.t2 * Data.t2 = 1) :
    Presentation.rowRelatorValues Data1792.first Data1792.second 6 = 1 := by
  exact nested_fourth_of_products hx hy hz hz2 hz3 ht ht2 hsq

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Relations1792.MixedWords
