module
public import Theory.SpecificGroups.PSL2.LargeOddInverter
/-!
# Split-torus primes inverted by binary PSL₂ involutions

The literal reflected split torus has order 2ⁿ−1. Cauchy's theorem
supplies any requested prime divisor, and involution fusion carries its
reflection to the prescribed involution without changing that order.

Source: Huppert II.8.3; Aschbacher--Smith E.2.17, printed p.230,
as used in the component argument of 12.6.26, printed p.832.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
/-- Every binary PSL₂ involution inverts an element of any prime order dividing the split torus. -/
theorem binary_involution_inverts_split_prime
    {F : Type*} [Field F] [Finite F] {n p : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (hp : p.Prime)
    (hd : p ∣ 2 ^ n - 1) (t : PSL(2,F)) (ht : orderOf t = 2) :
    ∃ x : PSL(2,F), orderOf x = p ∧ t * x * t⁻¹ = x⁻¹ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
    BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
  have ho : Odd (2 ^ n - 1) := by
    have he : Even ((2:ℕ)^n) := even_two.pow_of_ne_zero (by omega : n ≠ 0)
    have hpos : 0 < (2 : ℕ)^n := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by have := Nat.even_iff.mp he; omega)
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 := by
    rw [hF,Nat.coprime_iff_gcd_eq_one.mp ho.coprime_two_right]
  have hdiv : p ∣ Nat.card U := by rw [hcard,hgcd,Nat.div_one,hF]; exact hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := U) p hdiv
  have hwo : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2)
    (fun hh => hw (hh ▸ U.one_mem))
  obtain ⟨g,hg⟩ := isConj_iff.mp (involutions_isConj w t hwo ht)
  refine ⟨MulAut.conj g (x : PSL(2,F)),?_,?_⟩
  · rw [MulEquiv.orderOf_eq,Subgroup.orderOf_coe,hx]
  · rw [←hg]
    change (g*w*g⁻¹)*(g*(x:PSL(2,F))*g⁻¹)*(g*w*g⁻¹)⁻¹ = _
    calc
      _ = g*(w*(x:PSL(2,F))*w⁻¹)*g⁻¹ := by group
      _ = g*(x:PSL(2,F))⁻¹*g⁻¹ := by rw [hi x x.property]
      _ = _ := by simp only [MulAut.conj_apply]; group
end Theory.PSL2
