module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.ImageReduction
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters.Arithmetic
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension

/-!
# Conditional parameter reduction for odd symplectic FF actions

The faithful-image reduction retains the original binary space and full linear
normalizer. Bounds on automorphism two-rank and generation by conjugates then
bound its binary dimension. Combining this with the projective degree estimate
leaves six parameter pairs. Separate exclusions of the two nonternary rank-two
pairs and the three higher ternary pairs leave `(r,q) = (2,3)`.

All three estimates and the small-pair exclusions are explicit hypotheses.
Their construction, and hence the full parameter theorem, remains outstanding.
No absolute irreducibility or generalized-Fitting hypothesis on the full
normalizer is introduced. Source: Aschbacher–Smith B.1.13, printed pp.73–74;
Guralnick–Malle I, Proposition 4.5, author manuscript pp.12–13.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters

variable {L W : Type*} [Group L] [Finite L] [IsQuasisimple L]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  (σ : Representation (ZMod 2) L W)

/-- The original module is bounded using generation in its faithful image and
rank on the original group's literal central quotient. -/
theorem dimension_le_of_normalizer_estimates
    (hk : σ.ker ≤ center L) (hi : σ.IsIrreducible)
    (hff : IsFFModule (normalizerRepresentation σ)) {r : ℕ}
    (hgen : NormalizerConjugateGenerationBound (imageRepresentation σ) (2 * r + 1))
    (hrank : primeRank 2 (MulAut (L ⧸ center L)) ≤ 2 * r + 2) :
    Module.finrank (ZMod 2) W ≤ (2 * r + 1) * (2 * r + 2) := by
  let := actionImage_quasisimple σ hk
  exact finrank_le_of_ff_normalizer_central_quotient (imageRepresentation σ)
    (imageRepresentation_injective σ) (imageRepresentation_isIrreducible σ hi)
    (actionImage_quotientCenterEquiv σ hk).symm hgen hrank
    ((isFFModule_normalizer_imageRepresentation_iff σ).mpr hff)

/-- The actual source normalizer action has one of six parameter pairs,
conditional on the degree, automorphism-rank and conjugate-generation estimates. -/
theorem candidates_of_normalizer_estimates
    (hk : σ.ker ≤ center L) (hi : σ.IsIrreducible)
    (hff : IsFFModule (normalizerRepresentation σ)) {r q : ℕ}
    (ho : Odd q) (hr : 2 ≤ r) (hp : KnownSimple.SymplecticParameters r q)
    (hdegree : q ^ r ≤ 2 * Module.finrank (ZMod 2) W + 1)
    (hgen : NormalizerConjugateGenerationBound (imageRepresentation σ) (2 * r + 1))
    (hrank : primeRank 2 (MulAut (L ⧸ center L)) ≤ 2 * r + 2) :
    (r = 2 ∧ (q = 3 ∨ q = 5 ∨ q = 7)) ∨ ((r = 3 ∨ r = 4 ∨ r = 5) ∧ q = 3) := by
  have hdim := dimension_le_of_normalizer_estimates σ hk hi hff hgen hrank
  have hq1 := hp.1.one_lt
  have hq : 3 ≤ q := by obtain ⟨k, hk⟩ := ho; omega
  apply candidates hr hq ho
  apply hdegree.trans
  apply Nat.add_le_add_right
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hdim

/-- Assembly after the five small excluded pairs are discharged. This remains
conditional until the model estimates and both exclusions have been proved. -/
theorem parameters_of_estimates_and_small_exclusions
    (hk : σ.ker ≤ center L) (hi : σ.IsIrreducible)
    (hff : IsFFModule (normalizerRepresentation σ)) {r q : ℕ}
    (ho : Odd q) (hr : 2 ≤ r) (hp : KnownSimple.SymplecticParameters r q)
    (hdegree : q ^ r ≤ 2 * Module.finrank (ZMod 2) W + 1)
    (hgen : NormalizerConjugateGenerationBound (imageRepresentation σ) (2 * r + 1))
    (hrank : primeRank 2 (MulAut (L ⧸ center L)) ≤ 2 * r + 2)
    (htwo : r = 2 → q = 5 ∨ q = 7 → ¬ IsFFModule (normalizerRepresentation σ))
    (hthree : r = 3 ∨ r = 4 ∨ r = 5 → q = 3 →
      ¬ IsFFModule (normalizerRepresentation σ)) :
    r = 2 ∧ q = 3 := by
  rcases candidates_of_normalizer_estimates σ hk hi hff ho hr hp hdegree hgen hrank with
    ⟨hr2, hq3 | hq⟩ | ⟨hr345, hq3⟩
  · exact ⟨hr2, hq3⟩
  · exact (htwo hr2 hq hff).elim
  · exact (hthree hr345 hq3 hff).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddSymplecticOrthogonal.HigherSymplecticParameters
