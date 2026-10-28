module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Order-four lifts of binary quotient lines

Let N be an elementary abelian normal two-subgroup of a group whose quotient
by N is also elementary abelian. A subgroup with image of order two in the
quotient has a cyclic supplement modulo N. If its elements outside N cannot
be involutions, a generator of that supplement has order four.

This is the lifting step used after the quotient computation in Parrott,
*A characterization of the Tits' simple group* (1972), p.677.
-/

open Subgroup

namespace Subgroup

/-- A nontrivial binary quotient line with no involutory lifts has an
order-four lift which generates the subgroup modulo the elementary kernel. -/
public theorem exists_order_four_lift_of_quotient_card_two
    {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal]
    [IsElementaryAbelian 2 N] [IsElementaryAbelian 2 (G ⧸ N)]
    (hcard : Nat.card (K.map (QuotientGroup.mk' N)) = 2)
    (hno : ∀ b ∈ K, b ∉ N → orderOf b ≠ 2) :
    ∃ b ∈ K, orderOf b = 4 ∧ K ≤ zpowers b ⊔ N := by
  let q := QuotientGroup.mk' N
  let L := K.map q
  let : Nontrivial L := Finite.one_lt_card_iff_nontrivial.mp (by
    change 1 < Nat.card (K.map (QuotientGroup.mk' N))
    omega)
  obtain ⟨x, hx, hxne⟩ := L.exists_ne_one_of_nontrivial
  obtain ⟨b, hbK, rfl⟩ := hx
  have hbN : b ∉ N := fun hb => hxne ((QuotientGroup.eq_one_iff b).mpr hb)
  have hbq2 : (q b) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ N)) (q b)
  have hb2N : b ^ 2 ∈ N := (QuotientGroup.eq_one_iff _).mp (by
    change q (b ^ 2) = 1
    simpa only [map_pow] using hbq2)
  have hb4 : b ^ 4 = 1 := by
    simpa only [← pow_mul] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (b ^ 2) hb2N
  have horder : orderOf b = 4 := by
    have hd := orderOf_dvd_of_pow_eq_one hb4
    have hneone : orderOf b ≠ 1 := by
      intro heq
      exact hbN ((orderOf_eq_one_iff.mp heq).symm ▸ N.one_mem)
    have hnetwo := hno b hbK hbN
    have hchoices : orderOf b ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hchoices
    simp only [Finset.mem_insert, Finset.mem_singleton] at hchoices
    rcases hchoices with h1 | h2 | h4
    · exact False.elim (hneone h1)
    · exact False.elim (hnetwo h2)
    · exact h4
  have hline : zpowers (q b) = L := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem q hbK))
    rw [Nat.card_zpowers, orderOf_eq_prime hbq2 hxne]
    exact hcard.le
  refine ⟨b, hbK, horder, ?_⟩
  have hmap : K.map q ≤ (zpowers b).map q := by
    rw [MonoidHom.map_zpowers, hline]
  simpa only [q, QuotientGroup.ker_mk'] using (map_le_map_iff.mp hmap)

end Subgroup
