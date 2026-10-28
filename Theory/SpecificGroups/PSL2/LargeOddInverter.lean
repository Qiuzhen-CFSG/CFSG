module
public import BenderSuzuki.External.Huppert.II.theorem_8_3_split
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Mathlib.Data.Nat.Factors
/-!
# Large odd prime-power elements inverted by PSL₂ involutions

For an odd field of order greater than seven, its residue modulo four
selects one of the two reflected cyclic tori with odd order greater than
three. Its prime divisors and a cyclic generator supply an element of
odd prime-power order greater than three. Involution fusion carries its
reflection to the prescribed involution.

Source: Aschbacher–Smith E.2.17, printed p.230, using the dihedral subgroups
of orders q−1 and q+1 (Huppert II.8.3–4).
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
private theorem large_odd_cyclic_prime_power {G : Type*} [Group G] [Finite G]
    [IsCyclic G] (ho : Odd (Nat.card G)) (hl : 3 < Nat.card G) :
    ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < a ∧ 3 < p^a ∧ ∃ x : G, orderOf x = p^a := by
  by_cases h : ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card G ∧ p ≠ 3
  · obtain ⟨p,hp,hdiv,hp3⟩ := h
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hdiv)
    have hp4 : 3 < p := by have := hp.two_le; omega
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := G) p hdiv
    exact ⟨p,1,hp,hp2,by decide,by simpa using hp4,x,by simpa using hx⟩
  · have he : Nat.card G = 3 ^ (Nat.card G).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' (by
        intro p hp hd
        by_contra hn
        exact h ⟨p,hp,hd,hn⟩)
    obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
    refine ⟨3,_,by decide,by decide,?_,by omega,x,hx.trans he⟩
    by_contra hn
    have hz : (Nat.card G).primeFactorsList.length = 0 := by omega
    simp only [hz,pow_zero] at he
    omega

private theorem torus_large_inverter {F : Type*} [Field F] [Finite F]
    (U : Subgroup (PSL(2,F))) (hU : IsCyclic U) (ho : Odd (Nat.card U))
    (hlarge : 3 < Nat.card U) (w : PSL(2,F)) (hwU : w ∉ U) (hw2 : w*w=1)
    (hi : ∀ x∈U,w*x*w⁻¹=x⁻¹) (t : PSL(2,F)) (ht : orderOf t = 2) :
    ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < a ∧ 3 < p^a ∧
      ∃ x : PSL(2,F), orderOf x = p^a ∧ t*x*t⁻¹=x⁻¹ := by
  let := hU
  obtain ⟨p,a,hp,hp2,ha,hl,x,hx⟩ := large_odd_cyclic_prime_power ho hlarge
  have hw : orderOf w = 2 := orderOf_eq_prime (by simpa [pow_two] using hw2)
    (fun hh => hwU (hh ▸ U.one_mem))
  obtain ⟨c,hc⟩ := isConj_iff.mp (involutions_isConj w t hw ht)
  refine ⟨p,a,hp,hp2,ha,hl,c*(x:PSL(2,F))*c⁻¹,?_,?_⟩
  · change orderOf (MulAut.conj c (x:PSL(2,F))) = p^a
    rw [MulEquiv.orderOf_eq,Subgroup.orderOf_coe,hx]
  · rw [←hc]
    calc
      _ = c*(w*(x:PSL(2,F))*w⁻¹)*c⁻¹ := by group
      _ = c*(x:PSL(2,F))⁻¹*c⁻¹ := by rw [hi x x.property]
      _ = _ := by group

theorem exists_large_odd_prime_power_inverted
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n) (hl : 7 < Nat.card F)
    (hmod : Nat.card F % 8 = 1 ∨ Nat.card F % 8 = 7)
    (t : PSL(2,F)) (ht : orderOf t = 2) :
    ∃ r a : ℕ, r.Prime ∧ r ≠ 2 ∧ 0 < a ∧ 3 < r^a ∧
      ∃ x : PSL(2,F), orderOf x = r^a ∧ t*x*t⁻¹=x⁻¹ := by
  have hodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
    Nat.gcd_eq_right ((Nat.dvd_iff_mod_eq_zero).mpr (by omega))
  rcases hmod with hm | hm
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
    rw [hgcd] at hcard
    exact torus_large_inverter U hU (by rw [hcard]; exact Nat.odd_iff.mpr (by omega))
      (by rw [hcard]; omega) w hw hw2 hi t ht
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
    rw [hgcd] at hcard
    exact torus_large_inverter U hU (by rw [hcard]; exact Nat.odd_iff.mpr (by omega))
      (by rw [hcard]; omega) w hw hw2 hi t ht
/-- Every involution over an odd field of order greater than seven inverts
an element of odd prime-power order greater than three. -/
theorem exists_large_odd_prime_power_inverted_of_odd
    {F : Type*} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p^n) (hl : 7 < Nat.card F)
    (t : PSL(2,F)) (ht : orderOf t = 2) :
    ∃ r a : ℕ, r.Prime ∧ r ≠ 2 ∧ 0 < a ∧ 3 < r^a ∧
      ∃ x : PSL(2,F), orderOf x = r^a ∧ t*x*t⁻¹=x⁻¹ := by
  have hodd : Odd (Nat.card F) := hF ▸ ho.pow
  have hmod : Nat.card F % 4 = 1 ∨ Nat.card F % 4 = 3 := by
    have := Nat.odd_iff.mp hodd
    omega
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 2 :=
    Nat.gcd_eq_right ((Nat.dvd_iff_mod_eq_zero).mpr (by omega))
  rcases hmod with hm | hm
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_4_nonsplit_torus_reflection_data hF
    rw [hgcd] at hcard
    exact torus_large_inverter U hU (by rw [hcard]; exact Nat.odd_iff.mpr (by omega))
      (by rw [hcard]; omega) w hw hw2 hi t ht
  · obtain ⟨U,w,hU,hcard,_,hw,hw2,hi,_,_⟩ :=
      BenderSuzuki.External.huppert_II_8_3_split_torus_reflection_data hF
    rw [hgcd] at hcard
    exact torus_large_inverter U hU (by rw [hcard]; exact Nat.odd_iff.mpr (by omega))
      (by rw [hcard]; omega) w hw hw2 hi t ht

end Theory.PSL2
