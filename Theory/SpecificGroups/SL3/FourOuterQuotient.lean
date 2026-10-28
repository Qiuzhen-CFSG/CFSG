module
public import Theory.GroupTheory.SelfCentralizingOuter
public import Theory.SpecificGroups.PSL3Four.OuterThreeStructure.FieldTransport
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
/-!
# Noncyclic two-group extensions of SL₃(4)

A self-centralizing perfect normal subgroup marked as the full SL₃(4)
embeds the original quotient in Out(PSL₃(4)), whose order divides twelve.
A noncyclic two-group quotient therefore has order four and exponent two.
The marking descends by the actual center map; the scalar center is retained.

Source: Aschbacher–Smith 12.6.31(1), printed pp.836–837.
-/
public section
open Subgroup
private theorem kleinFour_of_card_dvd_twelve {A : Type*} [Group A] [Finite A] (hp : IsPGroup 2 A)
    (hn : ¬ IsCyclic A) (hd : Nat.card A ∣ 12) : IsKleinFour A := by
  obtain ⟨n,he⟩ := hp.exists_card_eq
  have hn2 : n ≤ 2 := by
    by_contra h
    have hn3 : 3 ≤ n := by omega
    have h8 : 8 ∣ Nat.card A := by
      rw [he]
      exact pow_dvd_pow 2 hn3
    have hh : 8 ∣ 12 := h8.trans hd
    norm_num at hh
  have hn1 : ¬ n ≤ 1 := by
    intro h
    apply hn
    apply isCyclic_of_card_dvd_prime (p := 2)
    rw [he]
    exact pow_dvd_pow 2 h
  have he4 : Nat.card A = 4 := by
    have : n = 2 := by omega
    rw [he,this]
    norm_num
  exact ⟨he4,(not_isCyclic_iff_exponent_eq_prime Nat.prime_two he4).mp hn⟩


open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

/-- The actual quotient of a self-centralizing full SL₃(4) component is E₄. -/
theorem isKleinFour_quotient_of_card_four {J F : Type*} [Group J] [Finite J]
    [Field F] [Finite F] (N : Subgroup J) [N.Normal] [Group.IsPerfect N]
    (e : N ≃* SL(3,F)) (hF : Nat.card F = 4)
    (hc : centralizer (N : Set J) ≤ N)
    (hp : IsPGroup 2 (J ⧸ N)) (hn : ¬ IsCyclic (J ⧸ N)) :
    IsKleinFour (J ⧸ N) := by
  let q : N ⧸ center N ≃* PSL(3,F) := QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro x hx
      exact ⟨e.symm x,((centerCongr e).symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)
  have hi := MulAut.centralQuotientOuter_comp_outerAction_injective N q hc
  have hd := (card_dvd_of_injective _ hi).trans
    (PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four hF)
  exact kleinFour_of_card_dvd_twelve hp hn hd
end Matrix.SpecialLinearGroup
