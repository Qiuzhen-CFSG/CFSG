module
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianCoordinates
public import Theory.ElementaryAbelian.Injective

/-!
# Large elementary actors in the Hermitian source image

An elementary actor with an outer involution has rank at most 2n+1:
conjugacy to the field involution puts its inner intersection in the marked
SL₃(2ⁿ) centralizer, and the outer image contributes at most one generator.
Consequently every larger elementary actor belongs to the literal component
image. The Chapter 12 consumer applies this to the original rank-saturated
offender, including n = 1. This supplies inner placement, not the later
parabolic or fixed-space classification.

Source: Aschbacher–Smith H.4.4(3–6), printed p.381, used in 8.2.4–5,
printed p.716 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian

/-- An elementary subgroup larger than the outer-centralizer bound belongs
to the actual component image. In particular every rank-4n actor is inner,
including at n = 1. -/
theorem large_elementary_le_image (n : ℕ) [NeZero n]
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) [IsElementaryAbelian 2 A]
    (hAN : A ≤ binaryNormalizer n) (hr : 2 * n + 1 < rank A) : A ≤ binaryImage n := by
  by_contra hn
  obtain ⟨i, hiA, hiL⟩ := SetLike.not_le_iff_exists.mp hn
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := A) i hiA)
    (fun h => hiL (h ▸ (binaryImage n).one_mem))
  obtain ⟨c, hc, hci⟩ := OuterRank.outer_involution_conjugate n (normalizerCoverage n)
    i (hAN hiA) hi2 hiL
  have hb := OuterRank.elementary_outer_twoRank_le n
    ⟨FieldSections.centralizerEquiv n⟩ A
    (OuterRank.Coefficients.elementary_relIndex_le_two n (normalizerCoverage n)
      A inferInstance hAN) i hiA c hc hci
  have htop : IsElementaryAbelian 2 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective _ (⊤ : Subgroup A).subtype_injective
  have hcard := (primeRank_le_iff_elementary_card_le A).mp hb ⊤ htop
  have hrank : rank A ≤ 2 * n + 1 := by
    have hl := Nat.log_mono_right (b := 2) hcard
    simpa only [Nat.card_congr topEquiv.toEquiv, Nat.log_pow Nat.one_lt_two, rank] using hl
  exact (not_lt_of_ge hrank) hr

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
