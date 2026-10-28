module

public import Theory.GroupTheory.C5C4ElementaryTwoSubgroup
public import Theory.GroupTheory.SpecificGroups.FiveFourInvolutionCentralizer

/-!
# Two-subgroups normalized by five in the faithful order-twenty group

Every two-subgroup of C5 semidirect C4 is cyclic of order dividing four.
An order-five group normalizing it acts trivially, since its automorphism
group has order at most two. If the two-subgroup were nontrivial, its
involution would have a centralizer containing five elements, contrary to
the order-four involution centralizer in the faithful semidirect product.

This elementary Frobenius-group argument supplies the quotient step in
Thompson VI, printed p.630, for the fixed-four centralizer core.
-/

open Subgroup
namespace SemidirectProduct

/-- A five-subgroup cannot normalize a nontrivial two-subgroup in the faithful model. -/
public theorem two_subgroup_eq_bot_of_five_normalizes
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (A U : Subgroup (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ))
    (hA : Nat.card A = 5) (hU : IsPGroup 2 U)
    (hAU : A ≤ normalizer (U : Set _)) : U = ⊥ := by
  let M := SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ
  let _ : Finite M := Finite.of_equiv _ equivProd.symm
  obtain ⟨hcyc, hdiv⟩ := two_subgroup_isCyclic_card_dvd_four φ U hU
  let _ := hcyc
  have hAut : Nat.card (MulAut U) ≤ 2 := by
    rw [IsCyclic.card_mulAut]
    have hd : Nat.card U ∣ 2 ^ 2 := hdiv
    obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    interval_cases n <;> norm_num only [Nat.reducePow] at hc <;> rw [hc] <;> decide
  let f : A →* MulAut U := U.normalizerMonoidHom.comp (inclusion hAU)
  have hfrange : Nat.card f.range = 1 := by
    have hd : Nat.card f.range ∣ 5 := by simpa only [hA] using card_range_dvd f
    have hb := (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans hAut
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact h
    · omega
  have hf (b : A) : f b = 1 := by
    have hbot : f.range = ⊥ := card_eq_one.mp hfrange
    exact mem_bot.mp (hbot ▸ show f b ∈ f.range from ⟨b, rfl⟩)
  by_contra hne
  have htwo : 2 ∣ Nat.card U := by
    have hd : Nat.card U ∣ 2 ^ 2 := hdiv
    obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hn0 : n ≠ 0 := by
      intro h
      exact hne (card_eq_one.mp (by simpa [h] using hc))
    rw [hc]
    exact dvd_pow_self 2 hn0
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  have hyG : orderOf (y : M) = 2 := (orderOf_injective U.subtype U.subtype_injective y).trans hy
  have hAC : A ≤ centralizer ({(y : M)} : Set M) := by
    intro b hb
    have hh := congrArg (fun a : MulAut U => (a y : M)) (hf ⟨b, hb⟩)
    change b * (y : M) * b⁻¹ = (y : M) at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh)
  have hb := card_le_of_le hAC
  rw [hA, (faithful_five_four_involution_centralizer φ hφ y hyG).2] at hb
  omega
end SemidirectProduct
