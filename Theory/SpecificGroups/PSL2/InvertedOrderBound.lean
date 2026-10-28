module
public import BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# Bounding an odd PSL2 field by its inverted element orders

An involution in odd PSL2(q) is conjugate to the reflection of each
standard cyclic torus. One of the tori of orders (q minus one)/2 and
(q plus one)/2 has odd order. A generator and involution fusion therefore
bound that torus by five whenever every nonidentity inverted odd-order
element has order three or five. Consequently q is at most eleven.

This uses the full element-order restriction, including composite orders;
no restriction just on prime divisors would suffice. The actual consumer
is the original marked component in Aschbacher--Smith 12.6.26, pp.832--833.
The reflected tori are Huppert II.8.3--4.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
private theorem reflected_odd_torus_card_le_five {F : Type*} [Field F] [Finite F]
    (U : Subgroup PSL(2,F)) (hU : IsCyclic U) (ho : Odd (Nat.card U))
    (w : PSL(2,F)) (hwU : w ∉ U) (hw2 : w*w=1)
    (hi : ∀ x∈U,w*x*w⁻¹=x⁻¹) (t : PSL(2,F)) (ht : orderOf t = 2)
    (horders : ∀ x : PSL(2,F), x ≠ 1 → Odd (orderOf x) →
      t*x*t⁻¹=x⁻¹ → orderOf x = 3 ∨ orderOf x = 5) : Nat.card U ≤ 5 := by
  by_cases hsmall : Nat.card U ≤ 1
  · omega
  let := hU
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  have hw : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2)
    (fun hh => hwU (hh ▸ U.one_mem))
  obtain ⟨c,hc⟩ := isConj_iff.mp (involutions_isConj w t hw ht)
  let y := c*(x:PSL(2,F))*c⁻¹
  have hy : orderOf y = Nat.card U := by
    change orderOf (MulAut.conj c (x:PSL(2,F))) = Nat.card U
    rw [MulEquiv.orderOf_eq,Subgroup.orderOf_coe,hx]
  have hy1 : y ≠ 1 := by intro hh; rw [hh,orderOf_one] at hy; omega
  have hinv : t*y*t⁻¹=y⁻¹ := by
    rw [←hc]
    change (c*w*c⁻¹)*(c*(x:PSL(2,F))*c⁻¹)*(c*w*c⁻¹)⁻¹=(c*(x:PSL(2,F))*c⁻¹)⁻¹
    calc
      _ = c*(w*(x:PSL(2,F))*w⁻¹)*c⁻¹ := by group
      _ = c*(x:PSL(2,F))⁻¹*c⁻¹ := by rw [hi x x.property]
      _ = _ := by group
  rcases horders y hy1 (hy ▸ ho) hinv with h | h <;> omega

/-- An inner involution in odd PSL2 which inverts only elements of orders
three and five among the nonidentity odd-order elements forces q at most eleven. -/
theorem odd_field_card_le_eleven_of_inverted_orders
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n)
    (t : PSL(2,F)) (ht : orderOf t = 2)
    (horders : ∀ x : PSL(2,F), x ≠ 1 → Odd (orderOf x) →
      t*x*t⁻¹=x⁻¹ → orderOf x = 3 ∨ orderOf x = 5) : Nat.card F ≤ 11 := by
  have hodd := Nat.odd_iff.mp (hF ▸ ho.pow)
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
    Nat.gcd_eq_right ((Nat.dvd_iff_mod_eq_zero).mpr (by omega))
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by omega
  rcases hmod with hm | hm
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
    rw [hgcd] at hcard
    have h := reflected_odd_torus_card_le_five U hU
      (by rw [hcard]; exact Nat.odd_iff.mpr (by omega)) w hw hw2 hi t ht horders
    rw [hcard] at h
    omega
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
    rw [hgcd] at hcard
    have h := reflected_odd_torus_card_le_five U hU
      (by rw [hcard]; exact Nat.odd_iff.mpr (by omega)) w hw hw2 hi t ht horders
    rw [hcard] at h
    omega
end Theory.PSL2
