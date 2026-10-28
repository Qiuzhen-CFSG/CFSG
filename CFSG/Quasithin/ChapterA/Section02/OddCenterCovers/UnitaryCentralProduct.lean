module

public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.MarkedCentralProductQuotient
public import Theory.GroupTheory.CubicIntersectionRankLower
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.Quasithin.CubicIntersectionLocalRank
public import Theory.NumberTheory.BinarySignedTorus
public import Mathlib.Algebra.Ring.GeomSum
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel

/-!
# The exceptional unitary central product in A.2.12(II)

The input consists of the actual commuting factors, their ordered product,
unitary model isomorphisms, and embedded center and intersection identities.
It contains neither the exceptional rank nor the arithmetic conclusion.
The central quotient comparison retains the specified scalar projections.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.12(II),
printed p.37. The fixed-field orders are 2ⁿ; the matrix fields have order 2²ⁿ.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

universe u

/-- Input to the exceptional calculation, before its rank and gcd conclusions. -/
structure UnitaryCentralProductData (H : Type u) [Group H] where
  first : Subgroup H
  second : Subgroup H
  distinct : first ≠ second
  first_quasisimple : IsQuasisimple first
  second_quasisimple : IsQuasisimple second
  commuting : first ≤ centralizer (second : Set H)
  product : ∀ h : H, ∃ a : first, ∃ b : second, (a : H) * b = h
  n₁ : ℕ
  n₂ : ℕ
  first_large : 3 ≤ n₁
  second_large : 3 ≤ n₂
  first_odd : Odd n₁
  second_odd : Odd n₂
  first_model : IsSpecialUnitaryModel first 3 (2 ^ n₁)
  second_model : IsSpecialUnitaryModel second 3 (2 ^ n₂)
  centers_eq : (center first).map first.subtype = (center second).map second.subtype
  intersection_eq : first ⊓ second = (center first).map first.subtype

variable {H : Type u} [Group H]

private theorem special_projection_kernel {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    {A : Type*} [Group A] (e : A ≃* J.specialSubgroup) :
    (J.specialToProjective.comp e.toMonoidHom).ker = center A := by
  have hk := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J hn hcard hc)
  ext a
  change e a ∈ J.specialToProjective.ker ↔ a ∈ center A
  rw [hk]
  constructor
  · intro ha
    have hh := (centerCongr e.symm ⟨e a, ha⟩).property
    change e.symm (e a) ∈ center A at hh
    rwa [e.symm_apply_apply] at hh
  · intro ha
    exact (centerCongr e ⟨a, ha⟩).property

/-- The quotient equivalence is induced by the exact scalar map in the supplied model. -/
theorem exists_special_centerQuotient_equiv {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) (hc : ∀ x, J.conj x = x ^ (2 ^ n))
    {A : Type*} [Group A] (e : A ≃* J.specialSubgroup) :
    ∃ q : (A ⧸ center A) ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∀ a, q (QuotientGroup.mk' (center A) a) = J.specialToProjective (e a) := by
  exact ⟨QuotientGroup.liftEquiv (center A)
    (J.specialToProjective_surjective.comp e.surjective)
    (special_projection_kernel J hn hcard hc e).symm, fun _ => rfl⟩

/-- The actual PSU₃ × PSU₃ quotient, retaining both original factor projections. -/
theorem UnitaryCentralProductData.exists_projective_product_equiv
    (d : UnitaryCentralProductData H)
    {F₁ F₂ : Type*} [Field F₁] [Finite F₁] [Field F₂] [Finite F₂]
    (J₁ : HermitianForm 3 F₁) (J₂ : HermitianForm 3 F₂)
    (hcard₁ : Nat.card F₁ = (2 ^ d.n₁) ^ 2)
    (hcard₂ : Nat.card F₂ = (2 ^ d.n₂) ^ 2)
    (hc₁ : ∀ x, J₁.conj x = x ^ (2 ^ d.n₁))
    (hc₂ : ∀ x, J₂.conj x = x ^ (2 ^ d.n₂))
    (e₁ : d.first ≃* J₁.specialSubgroup) (e₂ : d.second ≃* J₂.specialSubgroup) :
    ∃ e : (H ⧸ center H) ≃*
        (ProjectiveSpecialUnitaryMatrixGroup J₁ × ProjectiveSpecialUnitaryMatrixGroup J₂),
      ∀ (a : d.first) (b : d.second),
        e (QuotientGroup.mk' (center H) ((a : H) * b)) =
          (J₁.specialToProjective (e₁ a), J₂.specialToProjective (e₂ b)) := by
  obtain ⟨e, he⟩ := exists_centerQuotient_product_equiv d.first d.second d.commuting d.product
  obtain ⟨q₁, hq₁⟩ := exists_special_centerQuotient_equiv J₁
    (by have := d.first_large; omega) hcard₁ hc₁ e₁
  obtain ⟨q₂, hq₂⟩ := exists_special_centerQuotient_equiv J₂
    (by have := d.second_large; omega) hcard₂ hc₂ e₂
  refine ⟨e.trans (q₁.prodCongr q₂), fun a b => ?_⟩
  change (q₁ (e _).1, q₂ (e _).2) = _
  rw [he, hq₁, hq₂]

/-- The center of each actual odd-degree binary SU₃ model has order three. -/
theorem special_unitary_center_card_three [Finite H] {n : ℕ}
    (hn : 3 ≤ n) (ho : Odd n) (h : IsSpecialUnitaryModel H 3 (2 ^ n)) :
    Nat.card (center H) = 3 := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := h
  have hk := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J (by omega) hcard hc)
  rw [Nat.card_congr (centerCongr e).toEquiv, ← hk,
    HermitianForm.UniversalCover.card_kernel J hcard hc]
  apply Nat.gcd_eq_left_iff_dvd.mpr
  have hm := Nat.BinaryTorusParity.two_pow_mod_three n
  have hh := Nat.odd_iff.mp ho
  rw [hh] at hm
  norm_num at hm
  omega

/-- Both source factors have the original cubic center. -/
theorem UnitaryCentralProductData.factor_centers_card [Finite H]
    (d : UnitaryCentralProductData H) :
    Nat.card (center d.first) = 3 ∧ Nat.card (center d.second) = 3 :=
  ⟨special_unitary_center_card_three d.first_large d.first_odd d.first_model,
    special_unitary_center_card_three d.second_large d.second_odd d.second_model⟩

/-- The embedded source intersection has order exactly three. -/
theorem UnitaryCentralProductData.intersection_card [Finite H]
    (d : UnitaryCentralProductData H) : Nat.card (d.first ⊓ d.second : Subgroup H) = 3 := by
  rw [d.intersection_eq, card_map_of_injective d.first.subtype_injective]
  exact d.factor_centers_card.1

/-- The actual common center has at most three elements. -/
theorem UnitaryCentralProductData.intersection_card_le_three [Finite H]
    (d : UnitaryCentralProductData H) : Nat.card (d.first ⊓ d.second : Subgroup H) ≤ 3 := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := d.first_model
  have hk := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J
      (by have := d.first_large; omega) hcard hc)
  rw [d.intersection_eq, card_map_of_injective d.first.subtype_injective,
    Nat.card_congr (centerCongr e).toEquiv, ← hk]
  exact Nat.le_of_dvd (by decide) J.card_specialToProjective_ker_dvd_three

/-- The common factor intersection is a three-group, from the actual scalar kernel. -/
theorem UnitaryCentralProductData.intersection_isThreeGroup [Finite H]
    (d : UnitaryCentralProductData H) : IsPGroup 3 (d.first ⊓ d.second : Subgroup H) := by
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := d.first_model
  have hk := J.specialToProjective_ker_eq_center
    (HermitianForm.EvenProjectiveComparison.center_eq_bot J
      (by have := d.first_large; omega) hcard hc)
  have hcardZ : Nat.card (center d.first) ∣ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv, ← hk]
    exact J.card_specialToProjective_ker_dvd_three
  have hZ : IsPGroup 3 (center d.first) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hcardZ)
  rw [d.intersection_eq]
  exact hZ.map d.first.subtype

/-- The elementary diagonal subgroups supply the rank-three lower bound. -/
theorem UnitaryCentralProductData.three_le_primeRank [Finite H]
    (d : UnitaryCentralProductData H) : 3 ≤ primeRank 3 H := by
  apply three_le_primeRank_of_cubic_intersection d.first d.second d.commuting
    d.intersection_card_le_three
  · obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := d.first_model
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_special J
      (by have := d.first_large; omega) hcard hc d.first_odd
  · obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := d.second_model
    rw [primeRank_equiv 3 e]
    exact Theory.SpecificGroups.SignedThreeCubicRank.unitary_special J
      (by have := d.second_large; omega) hcard hc d.second_odd

private theorem common_prime {a b : ℕ} (ha : Odd a) (hb : Odd b)
    (h1 : Nat.gcd a b ≠ 1) (h3 : Nat.gcd a b ≠ 3) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ a + 1 ∧ p ∣ 2 ^ b + 1 := by
  let d := Nat.gcd a b
  have hdodd : Odd d := ha.of_dvd_nat (Nat.gcd_dvd_left a b)
  have hd3 : 3 < d := by
    have := Nat.odd_iff.mp hdodd
    change d ≠ 1 at h1
    change d ≠ 3 at h3
    omega
  obtain ⟨p, hp, hp3, hpd⟩ := Nat.BinarySignedTorus.exists_prime_gt_three_dvd_add hd3
  have hdA : 2 ^ d + 1 ∣ 2 ^ a + 1 := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left a b
    have hkodd : Odd k := ha.of_dvd_nat ⟨d, by simpa only [Nat.mul_comm] using hk⟩
    have hh := hkodd.nat_add_dvd_pow_add_pow (x := 2 ^ d) (y := 1)
    have hmul : d * k = _ := hk.symm
    simpa only [one_pow, ← pow_mul, hmul] using hh
  have hdB : 2 ^ d + 1 ∣ 2 ^ b + 1 := by
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_right a b
    have hkodd : Odd k := hb.of_dvd_nat ⟨d, by simpa only [Nat.mul_comm] using hk⟩
    have hh := hkodd.nat_add_dvd_pow_add_pow (x := 2 ^ d) (y := 1)
    have hmul : d * k = _ := hk.symm
    simpa only [one_pow, ← pow_mul, hmul] using hh
  exact ⟨p, hp, hp3, hpd.trans hdA, hpd.trans hdB⟩

/-- A common prime greater than three gives an actual forbidden two-local
normalizer. Only the individual-factor rank calculations are explicit. -/
theorem UnitaryCentralProductData.common_prime_obstruction [Finite H]
    (d : UnitaryCentralProductData H) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hloc : 1 ≤ twoLocalPrimeRank p d.first) (hrank : 2 ≤ primeRank p d.second) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      3 ≤ primeRank p (normalizer (R : Set H)) := by
  let : Fact p.Prime := ⟨hp⟩
  exact Theory.Quasithin.CubicIntersection.exists_normalizer_rank_three
    d.first d.second d.commuting d.intersection_isThreeGroup (by omega) hloc hrank

/-- A.2.12(II)'s gcd restriction follows from quasithinness and the
individual SU₃ torus ranks supplied by the local-rank calculation. -/
theorem UnitaryCentralProductData.gcd_eq [Finite H]
    (d : UnitaryCentralProductData H) (hH : IsQuasithin H)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → p ∣ 2 ^ d.n₁ + 1 →
      1 ≤ twoLocalPrimeRank p d.first)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → p ∣ 2 ^ d.n₂ + 1 →
      2 ≤ primeRank p d.second) :
    Nat.gcd d.n₁ d.n₂ = 1 ∨ Nat.gcd d.n₁ d.n₂ = 3 := by
  by_contra! hn
  obtain ⟨p, hp, hp3, hd₁, hd₂⟩ := common_prime d.first_odd d.second_odd hn.1 hn.2
  obtain ⟨R, hRne, hR, hr⟩ := d.common_prime_obstruction hp hp3
    (hloc p hp hp3 hd₁) (hrank p hp hp3 hd₂)
  have hb := isQuasithin_iff_twoLocal.mp hH (normalizer (R : Set H))
    ⟨R, hRne, hR, rfl⟩ p hp (hp.odd_of_ne_two (by omega))
  omega

/-- The original components give the source pair record after the genuine
gcd calculation; the record itself is never an input to that calculation. -/
noncomputable def UnitaryCentralProductData.toTheoremAUnitaryPair [Finite H]
    (d : UnitaryCentralProductData H) (hH : IsQuasithin H)
    (hfirst : IsComponent H d.first) (hsecond : IsComponent H d.second)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → p ∣ 2 ^ d.n₁ + 1 →
      1 ≤ twoLocalPrimeRank p d.first)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → p ∣ 2 ^ d.n₂ + 1 →
      2 ≤ primeRank p d.second) : TheoremAUnitaryPair H where
  first := d.first
  second := d.second
  first_component := hfirst
  second_component := hsecond
  product := d.product
  n₁ := d.n₁
  n₂ := d.n₂
  first_large := d.first_large
  second_large := d.second_large
  first_odd := d.first_odd
  second_odd := d.second_odd
  first_model := d.first_model
  second_model := d.second_model
  centers_eq := d.centers_eq
  gcd_eq := d.gcd_eq hH hloc hrank

end CFSG.Quasithin.ChapterA.Section02.OddCenterCovers
