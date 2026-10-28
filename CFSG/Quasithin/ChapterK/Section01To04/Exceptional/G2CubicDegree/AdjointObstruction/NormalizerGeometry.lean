module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.Inputs
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.AdjointObstruction.NormalizerGeometry.Operators

/-!
# The G₂ adjoint normalizer involution alternative

For the actual derivation action over a finite characteristic-two field of order
`2^r`, `r ≥ 2`, we construct all of `NormalizerCalculations`: faithfulness,
binary irreducibility, and the inner-or-half-dimension involution alternative.
The proof retains the genuine field actors and proves that the possible scalar
factor disappears in the inner involution case. The outer case has codimension
exactly `7*r`.

This supplies the normalizer input to the independent common-fixed-kernel
obstruction in `AdjointObstruction.lean`.
Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 8.2 and
Lemma 8.5, manuscript pp.53–56; see `G2CubicDegree/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
open Representation Representation.BinaryOffender Subgroup
attribute [local instance] ZMod.algebra
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

/-- The actual binary G₂ adjoint satisfies all normalizer calculations, including
the full normalizer's genuine outer field involutions. -/
theorem normalizerCalculations {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r) :
    NormalizerCalculations F r := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hr)
  refine ⟨NormalizerGeometry.binary_faithful F hq,
    NormalizerGeometry.binary_irreducible F, ?_⟩
  intro t ht
  obtain ⟨z, hz⟩ := Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hq
    (NormalizerGeometry.normalizerAutomorphism F hq t)
  by_cases hσ : z.right = 1
  · exact Or.inl (NormalizerGeometry.inner_involution_mem F hq t ht z hz hσ)
  · exact Or.inr (NormalizerGeometry.field_involution_codim F hq hF t ht z hz hσ).ge

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.AdjointObstruction
