module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.OrderArithmetic
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.SpecificGroups.SU3.PrimeOrderDivisibility
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.FixedFieldTwo
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.Mathieu.M22.Properties.Order

/-!
# Three-cover exclusions for the original A₆ maximality argument

An upper component whose order is divisible by 360, divides |GL₅(2)|,
and is not divisible by 64 cannot be one of the three-cover models.
The classical root groups exclude odd defining primes and binary fields
of exponent at least two. The remaining SU₃(2) group has order dividing
216. The exceptional covers have their literal quotient orders times three.

Source: Aschbacher–Smith, A.3.6 and 13.3.2, applied to the actual upper
component in the normal A₆ source configuration.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.CoverBounds
open Chapter1.Section02.LocalModels

variable {G : Type*} [Group G]

private theorem sixtyFour_dvd_cube {n : ℕ} (hn : 2 ≤ n) :
    64 ∣ (2 ^ n) ^ 3 := by
  change 2 ^ 6 ∣ (2 ^ n) ^ 3
  rw [← pow_mul]
  exact Nat.pow_dvd_pow 2 (by omega)

private theorem linear_cube {q : ℕ} (hm : IsSL G 3 q) :
    q ^ 3 ∣ Nat.card G := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv, ← hF]
  exact Matrix.ProjectiveSpecialLinearGroup.psl3_cube_dvd_card.trans
    (Subgroup.card_dvd_of_surjective (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective (center SL(3,F))))

private theorem not_linear (hdiv : Nat.card G ∣ 9999360)
    (hsmall : ¬64 ∣ Nat.card G) {q : ℕ}
    (hq : CoverParameter false q) (hm : IsSL G 3 q) : False := by
  have hc := linear_cube hm
  rcases hq with ⟨n, hn, rfl, hmod⟩ | ⟨hp, ho⟩
  · have hn2 : 2 ≤ n := by
      by_contra h
      have he : n = 1 := by omega
      norm_num [he] at hmod
    exact hsmall ((sixtyFour_dvd_cube hn2).trans hc)
  · exact OrderArithmetic.odd_cube_not_dvd_gl_five hp ho (hc.trans hdiv)

private theorem special_card_dvd_216 {F : Type*} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hF : Nat.card F = 2 ^ 2)
    (hconj : ∀ x, J.conj x = x ^ 2) :
    Nat.card J.specialSubgroup ∣ 216 := by
  have he := QuotientGroup.quotientKerEquivOfSurjective
    J.specialToProjective J.specialToProjective_surjective
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup J.specialToProjective.ker,
    Nat.card_congr he.toEquiv, HermitianForm.FixedFieldTwo.card_projective J hF hconj]
  exact Nat.mul_dvd_mul_left 72 J.card_specialToProjective_ker_dvd_three

private theorem not_unitary (hlarge : 360 ∣ Nat.card G)
    (hdiv : Nat.card G ∣ 9999360) (hsmall : ¬64 ∣ Nat.card G) {q : ℕ}
    (hq : CoverParameter true q) (hm : IsSU G 3 q) : False := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
  rcases hq with ⟨n, hn, rfl, _⟩ | ⟨hp, ho⟩
  · by_cases hn1 : n = 1
    · subst n
      have hd : Nat.card G ∣ 216 := by
        rw [Nat.card_congr e.toEquiv]
        exact special_card_dvd_216 J (by simpa using hF) (by simpa using hconj)
      exact (by decide : ¬360 ∣ 216) (hlarge.trans hd)
    · have hc := (HermitianForm.BinarySylowOrder.cube_dvd_card_projective J
          (by omega : n ≠ 0) hF hconj).trans
        (Subgroup.card_dvd_of_surjective J.specialToProjective
          J.specialToProjective_surjective)
      rw [← Nat.card_congr e.toEquiv] at hc
      exact hsmall ((sixtyFour_dvd_cube (by omega : 2 ≤ n)).trans hc)
  · have hc := J.prime_cube_dvd_card_special hp hF hconj
    rw [← Nat.card_congr e.toEquiv] at hc
    exact OrderArithmetic.odd_cube_not_dvd_gl_five hp ho (hc.trans hdiv)

private theorem threeCover_card [Finite G] {S : Type} [Group S]
    (hm : IsThreeCover G S) : Nat.card G = Nat.card S * 3 := by
  obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := hm
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center G),
    Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv]
  change Nat.card S * Nat.card (ZMod 3) = Nat.card S * 3
  rw [Nat.card_zmod]

/-- The literal A.3.6 three-cover catalogue is incompatible with the three
order constraints supplied by the source A₆ upper component. -/
theorem threeCover_excluded [Finite G]
    (hlarge : 360 ∣ Nat.card G) (hdiv : Nat.card G ∣ 9999360)
    (hsmall : ¬64 ∣ Nat.card G) (hm : ThreeCoverModel G) : False := by
  cases hm with
  | classical unitary q hq he =>
    cases unitary with
    | false => exact not_linear hdiv hsmall hq he
    | true => exact not_unitary hlarge hdiv hsmall hq he
  | alternating_six he =>
    rw [threeCover_card he, nat_card_alternatingGroup] at hdiv
    norm_num at hdiv
  | alternating_seven he =>
    rw [threeCover_card he, nat_card_alternatingGroup] at hdiv
    norm_num at hdiv
  | mathieu he =>
    rw [threeCover_card he, Sporadic.Mathieu.m22_order] at hdiv
    norm_num at hdiv

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.CoverBounds
