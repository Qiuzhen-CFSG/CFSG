module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianActors
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# The saturated Hermitian actor is the marked plane root group

The outer-centralizer rank bound puts a rank-4n elementary actor in the
actual component image. Sylow conjugacy and the fixed-space calculation
then mark it as the plane root group. Uniqueness inside a two-subgroup
supplies its relative normalization. Both assertions include n = 1.

The Chapter 12 application uses the original chosen-orbit automizer.
The preceding source saturation inputs and subsequent exclusions remain
with qt-d-1222-nonmathieu-hermitian-exclusion.

Source: Aschbacher–Smith H.4.4 and 8.2.5, printed pp.381 and716–717.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
variable (n : ℕ) [NeZero n]

/-- The full-normalizer version of the literal plane marking. -/
theorem saturated_actor_plane
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ binaryNormalizer n) (hA : rank A = 4*n)
    (hfix : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) A) = 4*n) :
    ∃ c : Cover n, A.map (MulAut.conj (binaryActionHom n c)).toMonoidHom =
      UnipotentRadicals.plane n := by
  apply UnipotentRadicals.maximal_elementary_plane_of_fixedRank n A
    (large_elementary_le_image n A hAN (by
      rw [hA]; have hn := NeZero.pos n; omega)) hA hfix

/-- The saturated actor is normalized by every two-subgroup containing it. -/
theorem saturated_actor_normalized
    (P : Subgroup (Space n ≃ₗ[ZMod 2] Space n))
    (hp : IsPGroup 2 P) (hPN : P ≤ binaryNormalizer n)
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAP : A ≤ P) (hA : rank A = 4*n)
    (hfix : Module.finrank (ZMod 2)
      (fixedSpace (UnipotentRadicals.ambientAction n) A) = 4*n) :
    P ≤ normalizer (A : Set (Space n ≃ₗ[ZMod 2] Space n)) := by
  apply UnipotentRadicals.le_normalizer_of_le_two_subgroup n P hp hPN A hAP
    (large_elementary_le_image n A (hAP.trans hPN) (by
      rw [hA]; have hn := NeZero.pos n; omega)) hA hfix

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
