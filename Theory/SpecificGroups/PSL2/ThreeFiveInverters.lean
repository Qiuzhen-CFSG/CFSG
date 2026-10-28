module
public import Theory.SpecificGroups.PSL2.LargeOddInverter
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# PSL₂ fields with only cubic and quintic inverted prime powers

Fix an involution in PSL₂ over an odd field of prime or prime-square order,
with the field order congruent to ±1 modulo eight. Involution fusion moves
its inverter onto either reflected torus. If every inverted odd prime-power
rotation has order three or five, every prime-power divisor of the odd torus
order divides fifteen. The torus order therefore divides fifteen, leaving
exactly fields of order seven and thirty-one.

Source application: Aschbacher–Smith 8.2.9, printed pp.720–721,
refs/quasithin.pdf (1 March 2004 manuscript). The reflected torus data are
Huppert II.8.3–4; no central-cover kernel is discarded here.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2.ThreeFiveInverters

private theorem odd_cyclic_card_dvd_fifteen {A : Type*} [Group A] [Finite A] [IsCyclic A]
    (ho : Odd (Nat.card A))
    (h : ∀ x : A, ∀ p a : ℕ, p.Prime → p ≠ 2 → 0 < a →
      orderOf x = p^a → orderOf x = 3 ∨ orderOf x = 5) : Nat.card A ∣ 15 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd 15 (Nat.card A)).mpr
  intro p a hp hd
  by_cases ha : a=0
  · simp [ha]
  have hpa : p ∣ Nat.card A := (dvd_pow_self p ha).trans hd
  have hp2 : p≠2 := by
    intro he
    rw [he] at hpa
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hpa)
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  have hd' : p^a ∣ orderOf x := hx ▸ hd
  have he := orderOf_pow_orderOf_div (show orderOf x≠0 by rw [hx]; exact Nat.card_pos.ne') hd'
  rcases h (x^(orderOf x/(p^a))) p a hp hp2 (by omega) he with h3 | h5
  · rw [←he,h3]; decide
  · rw [←he,h5]; decide

private theorem reflected_odd_torus_card {F : Type*} [Field F] [Finite F]
    (U : Subgroup PSL(2,F)) (hU : IsCyclic U) (ho : Odd (Nat.card U))
    (w : PSL(2,F)) (hw : w∉U) (hw2 : w*w=1)
    (hi : ∀ x∈U,w*x*w⁻¹=x⁻¹) (t : PSL(2,F)) (ht : orderOf t=2)
    (hrot : ∀ r : PSL(2,F), t*r*t⁻¹=r⁻¹ → ∀ p a : ℕ,
      p.Prime → p≠2 → 0<a → orderOf r=p^a → orderOf r=3 ∨ orderOf r=5) :
    Nat.card U ∣ 15 := by
  let := hU
  have hwc : orderOf w=2 := orderOf_eq_prime (by simpa only [pow_two] using hw2)
    (fun he => hw (he ▸ U.one_mem))
  obtain ⟨c,hc⟩ := isConj_iff.mp (involutions_isConj w t hwc ht)
  apply odd_cyclic_card_dvd_fifteen ho
  intro x p a hp hp2 ha hx
  let y : PSL(2,F) := c*(x:PSL(2,F))*c⁻¹
  have hy : orderOf y = orderOf x := by
    change orderOf (MulAut.conj c (x:PSL(2,F)))=orderOf x
    rw [MulEquiv.orderOf_eq,Subgroup.orderOf_coe]
  have hiy : t*y*t⁻¹=y⁻¹ := by
    rw [←hc]
    calc
      _ = c*(w*(x:PSL(2,F))*w⁻¹)*c⁻¹ := by dsimp [y]; group
      _ = c*(x:PSL(2,F))⁻¹*c⁻¹ := by rw [hi x x.property]
      _ = _ := by dsimp [y]; group
  simpa only [hy] using hrot y hiy p a hp hp2 ha (hy.trans hx)

private theorem divisor_fifteen_cases {n : ℕ} (h : n∣15) : n=1 ∨ n=3 ∨ n=5 ∨ n=15 := by
  have hn : n≤15 := Nat.le_of_dvd (by decide) h
  interval_cases n <;> norm_num at *

/-- The actual field order is seven or thirty-one under the marked inversion bound. -/
theorem field_card_eq_seven_or_thirty_one
    {F : Type*} [Field F] [Finite F] {p d : ℕ} [Fact p.Prime]
    (hp : 3<p) (hd : d=1 ∨ d=2) (hF : Nat.card F=p^d)
    (hmod : Nat.card F%8=1 ∨ Nat.card F%8=7)
    (t : PSL(2,F)) (ht : orderOf t=2)
    (hrot : ∀ r : PSL(2,F), t*r*t⁻¹=r⁻¹ → ∀ r₀ a : ℕ,
      r₀.Prime → r₀≠2 → 0<a → orderOf r=r₀^a → orderOf r=3 ∨ orderOf r=5) :
    Nat.card F=7 ∨ Nat.card F=31 := by
  have hprime : p.Prime := Fact.out
  have ho : Odd (Nat.card F) := hF ▸ (hprime.odd_of_ne_two (by omega)).pow
  have hgcd : Nat.gcd (Nat.card F-1) 2=2 :=
    Nat.gcd_eq_right ((Nat.dvd_iff_mod_eq_zero).mpr (by have := Nat.odd_iff.mp ho; omega))
  have hq : 3<Nat.card F := by
    rw [hF]
    rcases hd with rfl | rfl
    · simpa only [pow_one] using hp
    · nlinarith
  rcases hmod with hm | hm
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
    rw [hgcd] at hcard
    have huodd : Odd (Nat.card U) := by rw [hcard]; exact Nat.odd_iff.mpr (by omega)
    have hc := divisor_fifteen_cases (reflected_odd_torus_card U hU huodd w hw hw2 hi t ht hrot)
    rw [hcard] at hc
    have hq9 : Nat.card F=9 := by omega
    have hp9 : p≠9 := by intro he; exact (by decide : ¬Nat.Prime 9) (he ▸ hprime)
    rcases hd with rfl | rfl
    · simp only [pow_one] at hF; omega
    · nlinarith
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
    rw [hgcd] at hcard
    have huodd : Odd (Nat.card U) := by rw [hcard]; exact Nat.odd_iff.mpr (by omega)
    have hc := divisor_fifteen_cases (reflected_odd_torus_card U hU huodd w hw hw2 hi t ht hrot)
    rw [hcard] at hc
    omega

end Theory.PSL2.ThreeFiveInverters
