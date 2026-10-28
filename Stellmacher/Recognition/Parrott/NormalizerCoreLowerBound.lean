module

public import Stellmacher.Recognition.Parrott.SecondNormalizer
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.ElementaryThirtyTwoSolvableCore

/-!
# Transfer of the normalizer two-core bound through the actual action

For the supplied second elementary subgroup F, conjugation by N_G(F) has
kernel F, of order 32. The two-core therefore has order 32 times the
two-core of the actual automorphism image. This transfers the image bound
in Parrott's Lemma 6 without replacing F or its conjugation action.
Solvability and the linear-group bound give |O₂(N_G(F))| ≥ 512,
so the exceptional alternative in the source is unnecessary here.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, paragraph immediately after Lemma 5.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- The two-core order formula for the supplied F and its literal action. -/
public theorem normalizer_core_card_eq (d : ParrottSecondElementaryData z) :
    Nat.card (pCore 2 (normalizer (d.F : Set G))) =
      32 * Nat.card (pCore 2 d.F.normalizerMonoidHom.range) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 d.F := d.elementary
  have hker : IsPGroup 2 d.F.normalizerMonoidHom.ker := by
    rw [d.normalizer_action_ker]
    exact (IsElementaryAbelian.isPGroup 2 d.F).comap_subtype
  have hcard : Nat.card d.F.normalizerMonoidHom.ker = 32 := by
    rw [d.normalizer_action_ker,
      Nat.card_congr (subgroupOfEquivOfLe (H := d.F) le_normalizer).toEquiv, d.card]
  have hh := d.F.normalizerMonoidHom.rangeRestrict.card_pCore_of_ker_isPGroup
    d.F.normalizerMonoidHom.rangeRestrict_surjective (by
      rwa [MonoidHom.ker_rangeRestrict])
  rwa [MonoidHom.ker_rangeRestrict, hcard] at hh

/-- Transfer an image bound through the actual elementary kernel of order 32. -/
public theorem normalizer_core_lower_bound_of_image
    (d : ParrottSecondElementaryData z) (n : ℕ)
    (himage : (16 ≤ Nat.card (pCore 2 d.F.normalizerMonoidHom.range)) ∨
      (n = 21 ∧ 8 ≤ Nat.card (pCore 2 d.F.normalizerMonoidHom.range))) :
    (512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G)))) ∨
      (n = 21 ∧ 256 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G)))) := by
  rw [d.normalizer_core_card_eq]
  rcases himage with hh | ⟨hn, hh⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨hn, by omega⟩

/-- The linear-group bound transfers through the supplied action kernel F.
Only the relevant cardinal conclusions of `normalizer_card` are needed. -/
public theorem normalizer_core_card_ge_of_action_card
    (d : ParrottSecondElementaryData z) (hN : IsNTwoGroup G)
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31)
    (himage : Nat.card d.F.normalizerMonoidHom.range = 64 * n) :
    512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G))) := by
  let : IsElementaryAbelian 2 d.F := d.elementary
  let : Group.IsSolvable (normalizer (d.F : Set G)) := d.normalizer_solvable hN
  let : Group.IsSolvable d.F.normalizerMonoidHom.range :=
    Group.isSolvable_of_surjective d.F.normalizerMonoidHom.rangeRestrict_surjective
  have hbound := sixteen_le_card_two_core_of_solvable_elementary_thirtytwo_automorphisms
    d.card d.F.normalizerMonoidHom.range hnpos hnle himage
  rw [d.normalizer_core_card_eq]
  omega

/-- For any integer supplied by `normalizer_card`, the requested normalizer
core alternative holds; solvability always gives its first branch. -/
public theorem normalizer_core_lower_bound
    (d : ParrottSecondElementaryData z) (hN : IsNTwoGroup G)
    {n : ℕ} (hnpos : 1 ≤ n) (hnle : n ≤ 31)
    (himage : Nat.card d.F.normalizerMonoidHom.range = 64 * n) :
    (512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G)))) ∨
      (n = 21 ∧ 256 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G)))) := by
  exact Or.inl (d.normalizer_core_card_ge_of_action_card hN hnpos hnle himage)

/-- Under the original hypotheses, the actual normalizer two-core has order
at least 512, retaining the supplied second elementary subgroup. -/
public theorem normalizer_core_card_ge
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z)
    (hN : IsNTwoGroup G) :
    512 ≤ Nat.card (pCore 2 (normalizer (d.F : Set G))) := by
  obtain ⟨n, _, hnpos, hnle, _, himage⟩ := d.normalizer_card h
  exact d.normalizer_core_card_ge_of_action_card hN hnpos hnle himage

end Stellmacher.Recognition.ParrottSecondElementaryData
