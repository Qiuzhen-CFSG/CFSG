module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Inversion and odd-order normalizers

If the normalizer of a cyclic subgroup has odd order, its generator cannot
be conjugate to its inverse unless its square is one. A conjugating element
normalizes the cyclic subgroup. Its square centralizes the generator, and
an odd-order element is a power of its square.

This elementary observation supplies the two distinct eleven-classes in
Wong (1964), Theorem 6(a), p.107, DOI 10.1017/S1446788700022771.
-/

namespace Subgroup

/-- Odd-order cyclic normalizers cannot fuse a generator with its inverse,
except for elements whose square is one. -/
public theorem not_isConj_inv_of_odd_normalizer
    {G : Type*} [Group G] [Finite G] (x : G)
    (hodd : Odd (Nat.card (normalizer (zpowers x : Set G)))) (hx : x ^ 2 ≠ 1) :
    ¬ IsConj x x⁻¹ := by
  intro h
  obtain ⟨g, hg⟩ := isConj_iff.mp h
  have hgn : g ∈ normalizer (zpowers x : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    change zpowers (g * x * g⁻¹) = zpowers x
    rw [hg, zpowers_inv]
  obtain ⟨k, hk⟩ := hodd
  have hp : g ^ (2 * k + 1) = 1 := by
    have h := pow_card_eq_one' (x := (⟨g, hgn⟩ : normalizer (zpowers x : Set G)))
    have h' := congrArg Subtype.val h
    simpa only [Subgroup.coe_pow, OneMemClass.coe_one, hk, two_mul] using h'
  have h2 : Commute (g ^ 2) x := by
    have hi := congrArg (fun z : G => z⁻¹) hg
    simp only [mul_inv_rev, inv_inv] at hi
    apply mul_right_cancel (b := g⁻¹ * g⁻¹)
    calc
      _ = g * (g * x * g⁻¹) * g⁻¹ := by simp only [pow_two]; group
      _ = g * x⁻¹ * g⁻¹ := by rw [hg]
      _ = x := by simpa only [mul_assoc] using hi
      _ = _ := by group
  have he : g ^ (2 * (k + 1)) = g := by
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ, hp, one_mul]
  have hc : Commute g x := by simpa only [← pow_mul, he] using h2.pow_left (k + 1)
  have hi : x = x⁻¹ := by simpa only [hc.eq, mul_inv_cancel_right] using hg
  apply hx
  calc
    x ^ 2 = x * x := pow_two x
    _ = x * x⁻¹ := congrArg (x * ·) hi
    _ = 1 := mul_inv_cancel x

end Subgroup
