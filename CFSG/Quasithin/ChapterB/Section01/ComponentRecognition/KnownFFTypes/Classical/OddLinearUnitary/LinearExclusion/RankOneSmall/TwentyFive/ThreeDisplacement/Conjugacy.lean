module

public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# Order-three elements in the actual PSL₂(25) Borel complement

The projective diagonal complement has order twelve, so it contains an
order-three element. The checked PSL₂ order formula gives 7800, which is
not divisible by nine. Sylow conjugacy therefore places every order-three
element in a conjugate of this literal complement. No conjugacy-class table
or diagonalization assumption is required.

This supplies the group transport for the Borel-weight calculation in
Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript p.9, used by Aschbacher--Smith K.2, printed p.453.
-/

public section

open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup.OddBorel

variable {F : Type*} [Field F] [Finite F]

/-- Every order-three element of PSL₂(25) is conjugate into the literal
projective diagonal complement. -/
theorem order_three_conjugate_complement_of_card_twentyFive (hF : Nat.card F = 25)
    (x : PSL(2,F)) (hx : orderOf x = 3) :
    ∃ (c : complement F) (g : PSL(2,F)), orderOf c = 3 ∧
      x = g * (c : PSL(2,F)) * g⁻¹ := by
  classical
  let : Fintype (complement F) := Fintype.ofFinite _
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hC : Nat.card (complement F) = 12 := by rw [card_complement, hF]; norm_num
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card (G := complement F) 3 (by
    rw [← Nat.card_eq_fintype_card, hC]; norm_num)
  have hc' : orderOf (c : PSL(2,F)) = 3 :=
    (orderOf_injective (complement F).subtype Subtype.val_injective c).trans hc
  have horder : Nat.card PSL(2,F) = 7800 := by
    have he := psl2_card_twice (F := F) (by rw [hF]; decide)
    rw [hF] at he
    omega
  obtain ⟨k, g, hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 3) (by rw [horder]; norm_num) hc' hx
  refine ⟨c ^ k, g, ?_, ?_⟩
  · have he : orderOf ((c : PSL(2,F)) ^ k) = 3 := by
      rw [hg] at hx
      exact (MulEquiv.orderOf_eq (MulAut.conj g) ((c : PSL(2,F)) ^ k)).symm.trans hx
    simpa only [← map_pow] using
      (orderOf_injective (complement F).subtype Subtype.val_injective (c ^ k)).symm.trans he
  · simpa only [Subgroup.coe_pow] using hg

end Matrix.ProjectiveSpecialLinearGroup.OddBorel
