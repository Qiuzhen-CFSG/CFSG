module

public import Theory.SpecificGroups.SL2.CentralTwoExtensions

/-!
# Odd abelianization of SL₂

Every transvection in odd characteristic is the square of the transvection
with half its coefficient. Transvections generate SL₂, so squaring is
surjective on its abelianization. For a finite field this makes squaring
injective and excludes elements of order two in that abelianization.

The consumer in `UnitaryDerived` combines this with the cyclic/quaternion
Sylow calculation from `SL2.CentralTwoExtensions`. This treats the field of
three elements without a perfectness assumption. It supplies the small-field
part of the local GU₂ calculation supporting GLS3 §6.1 and the multiplier
results quoted in Aschbacher--Smith I.1.3--4.
-/

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
/-- The abelianization of finite SL₂ in odd characteristic has odd order,
including SL₂(3), which is not perfect. -/
public theorem odd_card_abelianization {F : Type*} [Field F] [Finite F]
    (hF : (2 : F) ≠ 0) : Odd (Nat.card (Abelianization SL(2, F))) := by
  let : Finite (Abelianization SL(2, F)) := by unfold Abelianization; infer_instance
  have hs : Function.Surjective (fun x : Abelianization SL(2, F) => x ^ 2) := by
    intro x
    obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator SL(2, F)) x
    change ∃ y : Abelianization SL(2, F), y ^ 2 = Abelianization.of A
    apply Matrix.SL2.transvection_induction
      (fun A => ∃ y : Abelianization SL(2, F), y ^ 2 = Abelianization.of A) ?_ ?_ A
    · intro i j hij c
      refine ⟨Abelianization.of (transvection hij (c / 2)), ?_⟩
      rw [← map_pow, pow_two, ← transvection_add, ← mul_two, div_mul_cancel₀ c hF]
    · intro A B hA hB
      obtain ⟨a, ha⟩ := hA
      obtain ⟨b, hb⟩ := hB
      exact ⟨a * b, by rw [mul_pow, ha, hb, map_mul]⟩
  have hi := (Finite.injective_iff_surjective).mpr hs
  apply Nat.not_even_iff_odd.mp
  intro h
  have hd : 2 ∣ Nat.card (Abelianization SL(2, F)) := even_iff_two_dvd.mp h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Abelianization SL(2, F)) 2 hd
  have hxpow : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have he : x = 1 := hi (hxpow.trans (one_pow 2).symm)
  simp [he] at hx
end Matrix.SpecialLinearGroup
