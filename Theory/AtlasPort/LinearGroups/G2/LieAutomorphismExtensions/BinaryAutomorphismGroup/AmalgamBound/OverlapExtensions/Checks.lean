module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.OverlapExtensions.Data

/-!
# Kernel certificates for the derived-overlap extensions

These finite checks certify the overlap multiplication and generation, exhaust
possible generator images, and verify the inverse permutations and generator
translations defining endpoint automorphisms. Only Lean's kernel evaluates
the certificates; no external group computation is trusted.

Source application: Aschbacher--Smith F.1.12(I)(8). Data provenance and ATLAS
attribution are in `Data` and its reproducible generator.
-/

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.OverlapExtensions

theorem middle_product : ∀ i j,
    leftTable.overlap (middleMul i j) =
      leftTable.mul (leftTable.overlap i) (leftTable.overlap j) := by decide +kernel

theorem middle_zero : leftTable.overlap 0 = 0 := by decide +kernel

theorem middle_words : ∀ i,
    leftTable.eval (leftTable.overlap 1) (leftTable.overlap 2) (middleWord i) =
      leftTable.overlap i := by decide +kernel

theorem middle_relations :
    middleMul (middleMul 1 1) (middleMul 1 1) ≠ 0 ∧
    middleMul 2 2 = 0 ∧
    middleMul (middleMul (middleMul 1 2) (middleMul 1 2))
      (middleMul (middleMul 1 2) (middleMul 1 2)) = 0 := by decide +kernel

theorem image_coverage : ∀ x y : Fin 32,
    middleMul (middleMul x x) (middleMul x x) ≠ 0 →
    middleMul y y = 0 →
    middleMul (middleMul (middleMul x y) (middleMul x y))
      (middleMul (middleMul x y) (middleMul x y)) = 0 →
    ∃ k : Fin 32, x = firstImage k ∧ y = secondImage k := by decide +kernel

theorem extension_inverse : ∀ k i, inverse k (extension k i) = i := by decide +kernel

theorem inverse_extension : ∀ k i, extension k (inverse k i) = i := by decide +kernel

theorem extension_zero : ∀ k, extension k 0 = 0 := by decide +kernel

theorem extension_step : ∀ k (b : Bool) i,
    extension k (leftTable.mul (if b then 2 else 1) i) =
      leftTable.mul (if b then extension k 2 else extension k 1) (extension k i) := by
  decide +kernel

theorem extension_generators : ∀ k,
    extension k (leftTable.overlap 1) = leftTable.overlap (firstImage k) ∧
    extension k (leftTable.overlap 2) = leftTable.overlap (secondImage k) := by decide +kernel

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound.OverlapExtensions
