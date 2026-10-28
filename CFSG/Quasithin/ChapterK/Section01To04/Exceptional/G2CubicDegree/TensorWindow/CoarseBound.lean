module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow
public import Theory.Representation.BinaryOffender.QuasisimpleCardBound.ThresholdTwo.Supplement
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# The coarse threshold-two degree bound for G₂

For the actual join H of the G₂ action image and the normalizer actor A,
threshold-two maximization gives |V| ≤ |H|². Normalization gives
|H| ≤ |G₂(2ʳ)| |A|. The G₂ order is strictly below 2^(14*r), and the
explicit automorphism two-rank hypothesis bounds |A| by 2^(3*r).
Consequently the binary degree is strictly below 34*r.

This discharges the `hcoarse` input of
`TensorWindow.window_of_coarse_and_half_tensor_estimates`. The automorphism
rank estimate remains explicit, as in that consumer; cubicity is unnecessary.

Source: Guralnick–Malle, Classification of 2F-modules II, §2.1 Lemma 2.1
and §3.5 equation (3.3); see `G2CubicDegree/Source.md`.
-/

public section
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.QuasisimpleNormalizer
open Subgroup Theory.GroupTheory

variable {F V : Type*} [Field F] [Finite F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [IsIrreducible σ]

private theorem g2_card_lt {r : ℕ} (hF : Nat.card F = 2 ^ r) :
    Nat.card (Atlas.G2.Model F) < 2 ^ (14 * r) := by
  rw [Atlas.G2.card_Model, hF]
  have h6 : (2 ^ r) ^ 6 - 1 < (2 ^ r) ^ 6 :=
    Nat.sub_lt (by positivity) (by decide)
  calc
    (2 ^ r) ^ 6 * ((2 ^ r) ^ 6 - 1) * ((2 ^ r) ^ 2 - 1) ≤
        (2 ^ r) ^ 6 * ((2 ^ r) ^ 6 - 1) * (2 ^ r) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ < (2 ^ r) ^ 6 * (2 ^ r) ^ 6 * (2 ^ r) ^ 2 :=
      Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_left h6 (by positivity)) (by positivity)
    _ = 2 ^ (14 * r) := by rw [← pow_add, ← pow_add, ← pow_mul]; congr 1; omega

/-- The exact coarse estimate used by the G₂ tensor-window reduction. -/
theorem degree_lt_thirtyFour_of_small_actor [CharP F 2]
    {r : ℕ} (_hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V < 34 * r := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  have hrank : rank A ≤ 3 * r :=
    rank_le_of_primeRank_le hA (normalizer_rank_le σ hf hAut)
  have hAcard : Nat.card A ≤ 2 ^ (3 * r) := by
    rw [hA.card_eq_two_pow_rank]
    exact Nat.pow_le_pow_right (by decide) hrank
  have hfaith : Function.Injective σ.asGroupHom := by
    intro g h he
    exact hf (congrArg Units.val he)
  let e : Atlas.G2.Model F ≃* actionImage σ := MonoidHom.ofInjective hfaith
  have hcardImage : Nat.card (actionImage σ) = Nat.card (Atlas.G2.Model F) :=
    (Nat.card_congr e.toEquiv).symm
  have hH : Nat.card (supplement σ A) < 2 ^ (17 * r) := by
    calc
      Nat.card (supplement σ A) ≤ Nat.card (actionImage σ) * Nat.card A :=
        card_supplement_le σ A
      _ ≤ Nat.card (Atlas.G2.Model F) * 2 ^ (3 * r) := by
        rw [hcardImage]
        exact Nat.mul_le_mul_left _ hAcard
      _ < 2 ^ (14 * r) * 2 ^ (3 * r) :=
        Nat.mul_lt_mul_of_pos_right (g2_card_lt hF) (by positivity)
      _ = 2 ^ (17 * r) := by rw [← pow_add]; congr 1; omega
  have hV : Nat.card V < 2 ^ (34 * r) := by
    calc
      Nat.card V ≤ Nat.card (supplement σ A) ^ 2 :=
        card_le_supplement_sq_of_small_actor σ A hA hsmall
      _ < (2 ^ (17 * r)) ^ 2 := Nat.pow_lt_pow_left hH (by decide)
      _ = 2 ^ (34 * r) := by rw [← pow_mul]; congr 1; omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod] at hV
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hV

/-- With the coarse estimate discharged, only the half-field tensor estimate
remains in the source tensor-window consumer (besides its explicit rank input). -/
theorem window_of_half_tensor_estimate [CharP F 2]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ)
    (hAut : primeRank 2 (MulAut (Atlas.G2.Model F)) ≤ 3 * r)
    (hhalf : Module.finrank (ZMod 2) V = 18 * r →
      ∀ t : linearNormalizer σ, t ≠ 1 → t ^ 2 = 1 →
        Representation.BinaryOffender.SchurNormalizer.IsSchurLinear σ t →
        5 * Module.finrank (ZMod 2) V ≤
          12 * fixedCodim (normalizerRepresentation σ) (zpowers t)) :
    ∀ A : Subgroup (linearNormalizer σ),
      IsElementaryTwo A → IsCubic (normalizerRepresentation σ) A →
      fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A →
      Module.finrank (ZMod 2) V < 18 * r :=
  window_of_coarse_and_half_tensor_estimates σ hr hF hf hAut
    (degree_lt_thirtyFour_of_small_actor σ hr hF hf hAut) hhalf

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow
